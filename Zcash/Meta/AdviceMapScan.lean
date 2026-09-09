import Zcash.Meta.SourceReduction
import Zcash.Meta.CertificateChunks
import Zcash.Snark.ZeroKnowledge.AdviceMapScan

/-!
# Bounded kernel checks for source-order map scans

Each continuation contains the actual option-valued transitions. Intermediate
maps are reduced to constructor data and checked as ordinary definitions. The
completed proof composes those checked continuations. A failed transition is an
error; no compiled evaluator, axiom, or assumed scan result is used.
-/

namespace Zcash.Meta
open Lean Meta Elab Tactic
open Zcash.Snark.ZeroKnowledge

register_option Zcash.adviceMapScan.chunkEntries : Nat := {
  defValue := 64
  descr := "maximum advice-map entries in each synchronous kernel check"
}

initialize registerTraceClass `Zcash.adviceMapScan

private def mapScanTarget (step roots entries : Expr) : MetaM Expr := do
  mkEq (← mkAppM ``adviceMapScan #[step, roots, entries]) (mkConst ``Bool.true)

private def checkedMapState (roots : Expr) : MetaM Expr := do
  let normalized ← SourceReduction.reduceConstructorData roots
  let name ← mkAuxDeclName
  withOptions (Elab.async.set · false) do
    mkAuxDefinition name (← inferType roots) normalized (compile := false)

/-- Check the exact source-order scan in bounded, kernel-checked continuations. -/
elab "check_advice_map_scan" : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let originalGoal ← getMainGoal
    let originalTarget ← originalGoal.getType
    let some (_, lhs, rhs) := originalTarget.eq? | throwError "expected a Boolean scan equality"
    unless lhs.isAppOf ``adviceMapScan && rhs.isConstOf ``Bool.true do
      throwError "expected adviceMapScan ... = true"
    let arguments := lhs.getAppArgs
    let step := arguments[1]!
    let mut roots := arguments[2]!
    let mut entries := arguments[3]!
    let savedMCtx ← getMCtx
    let mut first ← mkFreshExprMVar originalTarget
    let mut goal := first.mvarId!
    let mut chunks : Array Expr := #[]
    let chunkEntries := max 1 (Zcash.adviceMapScan.chunkEntries.get (← getOptions))
    for count in [:200000] do
      if count > 0 && count % chunkEntries == 0 then
        roots ← checkedMapState roots
        let target ← mapScanTarget step roots entries
        let next ← mkFreshExprMVar target
        goal.assign next
        chunks := chunks.push (← checkCertificateChunk first.mvarId! next.mvarId! false)
        if target.hasMVar || chunks.back!.hasMVar then throwError "unresolved map-scan boundary"
        setMCtx savedMCtx
        resetCache
        first ← mkFreshExprMVar target
        goal := first.mvarId!
        if ← isTracingEnabledFor `Zcash.adviceMapScan then
          IO.eprintln s!"[advice map scan] kernel checked {count} entries"
      let reduced ← withTransparency .all (whnf entries)
      if reduced.isAppOf ``List.nil then
        goal.assign (← mkEqRefl (mkConst ``Bool.true))
        let mut value ← checkCertificateValue first.mvarId! false
        for chunk in chunks.reverse do value := mkApp chunk value
        originalGoal.assign value
        if ← isTracingEnabledFor `Zcash.adviceMapScan then
          IO.eprintln s!"[advice map scan] complete: {count} entries"
        replaceMainGoal []
        return
      unless reduced.isAppOf ``List.cons do throwError "cannot reduce source entry {count} to a list constructor"
      let listArguments := reduced.getAppArgs
      let entry := listArguments[1]!
      let rest := listArguments[2]!
      let transition := mkApp2 step roots entry
      let result ← withTransparency .all (whnf transition)
      unless result.isAppOf ``Option.some do
        throwError "original advice-map policy rejects entry {count}"
      let nextRoots := result.getAppArgs.back!
      let next ← mkFreshExprMVar (← mapScanTarget step nextRoots rest)
      let hstep ← mkEqRefl result
      let proof ← mkAppM ``adviceMapScan_cons #[step, roots, nextRoots, entry, rest, hstep, next]
      goal.assign proof
      goal := next.mvarId!
      roots := nextRoots
      entries := rest
    throwError "advice-map scan entry limit reached"

end Zcash.Meta
