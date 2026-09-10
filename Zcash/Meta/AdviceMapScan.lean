import Zcash.Meta.SourceReduction
import Zcash.Meta.CertificateChunks
import Zcash.Snark.ZeroKnowledge.AdviceMapScan
import Zcash.Snark.ZeroKnowledge.AdviceMapScanPiece
import Zcash.Snark.ZeroKnowledge.AdviceReadAddressScan

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

private def checkedMapState (roots : Expr) (compile : Bool := false) : MetaM Expr := do
  let normalized ← SourceReduction.reduceConstructorData roots
  let name ← mkAuxDeclName
  withOptions (Elab.async.set · false) do
    mkAuxDefinition name (← inferType roots) normalized (compile := compile)

-- WHNF can leave a reducible source wrapper in a recursor's major premise.
-- Expose that premise definitionally before asking for its opaque equation.
private partial def exposeTransitionData (expression : Expr) : MetaM Expr := do
  let reduced ← withTransparency .all (whnf expression)
  let some name := reduced.getAppFn.constName? | return reduced
  let mut arguments := reduced.getAppArgs
  match (← getEnv).find? name with
  | some (.ctorInfo info) =>
    for index in [info.numParams:arguments.size] do
      unless ← isProof arguments[index]! do
        arguments := arguments.set! index (← exposeTransitionData arguments[index]!)
    return mkAppN reduced.getAppFn arguments
  | some (.recInfo info) =>
    let index := info.getMajorIdx
    let major ← exposeTransitionData arguments[index]!
    if major == arguments[index]! then return reduced
    exposeTransitionData (mkAppN reduced.getAppFn (arguments.set! index major))
  | _ => return reduced

-- Normalize source metadata before constructing the policy's dependent
-- decidability proofs. The source-to-data equality itself is kernel checked.
private def normalizeAddressData (original : Expr) : MetaM (Expr × Expr) := do
  let mut current := original
  let mut equality ← mkEqRefl original
  for _ in [:10000] do
    let before := current
    let (normalized, proof) ← SourceReduction.normalizeSourceData current
    equality ← mkEqTrans equality proof
    current := normalized
    if current != before then continue
    try
      let (next, proof?) ← SourceReduction.sourceReductionStep current
      if let some proof := proof? then equality ← mkEqTrans equality proof
      current := next
    catch _ =>
      let checked ← withOptions (Elab.async.set · false) do
        withTransparency .all <| mkAuxTheorem (← mkEq original current) equality
      return (current, checked)
  throwError "address source normalization limit reached"

private def reduceReadSourceTransition (transition : Expr) : MetaM (Expr × Expr) := do
  let arguments := transition.getAppArgs
  let place := arguments[arguments.size - 3]!
  let roots := arguments[arguments.size - 2]!
  let entry := arguments.back!
  let original ← mkAppM ``adviceReadAddressData #[place, entry]
  let (normalized, hdata) ← normalizeAddressData original
  let reader := mkApp (mkConst ``adviceReadAddressMapStep) roots
  let result ← withTransparency .all (whnf (mkApp reader normalized))
  let hfactor ← mkAppM ``adviceReadMapStep_eq_addressStep #[place, roots, entry]
  let equality ← withTransparency .all <| mkEqTrans hfactor (← mkCongrArg reader hdata)
  return (result, equality)

/-- Normalize only an alias entry before applying the original map policy.
In particular, simplification never traverses the accumulated root map. -/
private def reduceAliasSourceTransition (transition : Expr) : MetaM (Expr × Expr) := do
  let arguments := transition.getAppArgs
  let roots := arguments[arguments.size - 2]!
  let entry := arguments.back!
  let current ← exposeTransitionData entry
  let rules ← ({} : SimpTheorems).addDeclToUnfold ``Zcash.Circuits.Ecc.MulComplete.zWit
  let rules ← rules.addDeclToUnfold ``Zcash.Circuits.Ecc.MulComplete.yPWit
  let rules ← rules.addDeclToUnfold ``Witgen.MOver.toIRScalar
  let context ← Simp.mkContext { failIfUnchanged := false, maxSteps := 100000 }
    (simpTheorems := #[rules])
  let (simplified, _) ← simp current context
  let hentry ← match simplified.proof? with
    | some proof => pure proof
    | none => mkEqRefl entry
  let (normalized, hdata) ← normalizeAddressData simplified.expr
  let reader := mkApp (mkConst ``adviceAliasMapStep) roots
  let result ← withTransparency .all (whnf (mkApp reader normalized))
  let equality ← withTransparency .all <| mkCongrArg reader (← mkEqTrans hentry hdata)
  return (result, equality)

/-- Expose a blocked source transition through its original defining equations.
The simplifier preserves dependent matcher motives while opening scalar IR
wrappers. Source-owned projection equations handle the remaining placed cells.
The returned equality is retained in the eventual kernel-checked map step. -/
private def reduceSourceTransition (transition : Expr) : MetaM (Expr × Expr) := do
  let mut current ← withTransparency .all (whnf transition)
  let mut equality ← mkEqRefl transition
  if current.isAppOf ``Option.some || current.isAppOf ``Option.none then
    return (current, equality)
  if transition.isAppOf ``adviceReadMapStep then
    return ← reduceReadSourceTransition transition
  if transition.isAppOf ``adviceAliasMapStep then
    return ← reduceAliasSourceTransition transition
  for _ in [:10000] do
    current ← exposeTransitionData current
    if current.isAppOf ``Option.some || current.isAppOf ``Option.none then
      return (current, equality)
    let (next, proof?) ← SourceReduction.sourceReductionStep current
    if let some proof := proof? then equality ← mkEqTrans equality proof
    current := next
  throwError "source transition reduction limit reached"

/-- Check a bounded prefix, preserving the map and every unprocessed entry.
Each declaration produces a continuation that requires the remaining scan. -/
elab "check_advice_map_piece " limit:num : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let originalGoal ← getMainGoal
    let target ← originalGoal.getType
    unless target.isAppOf ``AdviceMapScanPiece do
      throwError "expected an AdviceMapScanPiece goal"
    let arguments := target.getAppArgs
    let step := arguments[arguments.size - 3]!
    let mut roots := arguments[arguments.size - 2]!
    let mut entries := arguments.back!
    let first ← mkFreshExprMVar (← mapScanTarget step roots entries)
    let mut goal := first.mvarId!
    let mut count : Nat := 0
    let compilePieces := !(← readThe Term.Context).isNoncomputableSection &&
      !(← Term.getDeclName?).any (Lean.isNoncomputable (← getEnv))
    for _ in [:limit.getNat] do
      let reduced ← withTransparency .all (whnf entries)
      if reduced.isAppOf ``List.nil then
        entries := reduced
        break
      unless reduced.isAppOf ``List.cons do
        throwError "cannot reduce source entry {count} to a list constructor"
      let listArguments := reduced.getAppArgs
      let entry := listArguments[1]!
      let rest := listArguments[2]!
      let (result, hstep) ← reduceSourceTransition (mkApp2 step roots entry)
      unless result.isAppOf ``Option.some do
        if result.isAppOf ``Option.none then
          throwError "original advice-map policy rejects entry {count}"
        else
          throwError "cannot expose the source transition at entry {count}"
      let nextRoots := result.getAppArgs.back!
      let next ← mkFreshExprMVar (← mapScanTarget step nextRoots rest)
      goal.assign (← withTransparency .all <|
        mkAppM ``adviceMapScan_cons #[step, roots, nextRoots, entry, rest, hstep, next])
      goal := next.mvarId!
      roots := nextRoots
      entries := rest
      count := count + 1
    if count > 0 then roots ← checkedMapState roots compilePieces
    -- Compiled records must not retain reduction-only list auxiliaries.
    if compilePieces then entries ← SourceReduction.reduceConstructorData entries
    let remaining ← mkFreshExprMVar (← mapScanTarget step roots entries)
    goal.assign remaining
    let continuation ← checkCertificateChunk first.mvarId! remaining.mvarId! false
    -- The source and initial map are already fixed by the goal. Store that
    -- fully indexed record through the kernel without re-inferring its indices
    -- from a large recursive scan. Local let bindings are closed by expansion.
    let record := mkAppN (mkConst ``AdviceMapScanPiece.mk)
      (arguments ++ #[roots, entries, continuation])
    let stored ← withOptions (Elab.async.set · false) do
      mkAuxDefinition (← mkAuxDeclName) target record
        (zetaDelta := true) (compile := compilePieces)
    originalGoal.assign stored
    if ← isTracingEnabledFor `Zcash.adviceMapScan then
      IO.eprintln s!"[advice map piece] {← Term.getDeclName?}: checked {count} entries; remainder empty: {entries.isAppOf ``List.nil}"
    replaceMainGoal []

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
      let (result, hstep) ← reduceSourceTransition transition
      unless result.isAppOf ``Option.some do
        if result.isAppOf ``Option.none then
          throwError "original advice-map policy rejects entry {count}"
        else
          throwError "cannot expose the source transition at entry {count}"
      let nextRoots := result.getAppArgs.back!
      let next ← mkFreshExprMVar (← mapScanTarget step nextRoots rest)
      let proof ← withTransparency .all <|
        mkAppM ``adviceMapScan_cons #[step, roots, nextRoots, entry, rest, hstep, next]
      goal.assign proof
      goal := next.mvarId!
      roots := nextRoots
      entries := rest
    throwError "advice-map scan entry limit reached"

end Zcash.Meta
