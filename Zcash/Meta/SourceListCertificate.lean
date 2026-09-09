import Zcash.Meta.SourceReduction
import Zcash.Snark.ZeroKnowledge.SourceListCertificate

/-!
# Reflecting finite metadata from the original circuit source

The elaborator retains each source entry and every opaque-source equality in a
certificate checked synchronously by the kernel. The normalized entries are
static proof metadata; no successful routing check is inferred by this command.
-/

namespace Zcash.Meta

open Lean Meta Elab Tactic SourceReduction
open Zcash.Snark.ZeroKnowledge

initialize registerTraceClass `Zcash.sourceListCertificate

private def listCertificateProgress (message : String) : MetaM Unit := do
  if ← isTracingEnabledFor `Zcash.sourceListCertificate then
    IO.eprintln s!"[source list] {message}"

/-- Certify the exact list produced by a source projection, using only checked equalities. -/
elab "certify_source_list" : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let originalGoal ← getMainGoal
    let originalTarget ← originalGoal.getType
    unless originalTarget.isAppOf ``SourceListCertificate do
      throwError "expected a SourceListCertificate goal"
    let elementType := originalTarget.getAppArgs[0]!
    let mut goal := originalGoal
    let mut currentSource := originalTarget.getAppArgs.back!
    let mut count := 0
    for step in [:200000] do
      if step % 1000 == 0 then listCertificateProgress s!"step {step}: {count} entries"
      let reduced ← withTransparency .all (whnf currentSource)
      if reduced.isAppOf ``List.nil then
        goal.assign (← mkAppOptM ``SourceListCertificate.nil #[some elementType])
        let value ← instantiateMVars (mkMVar originalGoal)
        if value.hasMVar then throwError "unresolved source-list certificate values"
        let name ← mkAuxDeclName
        let _ ← withOptions (Elab.async.set · false) do
          mkAuxDefinition name originalTarget value (compile := false)
        listCertificateProgress s!"kernel checked {count} source entries"
        replaceMainGoal []
        return
      if reduced.isAppOf ``List.cons then
        let arguments := reduced.getAppArgs
        let entry := arguments[1]!
        let rest := arguments[2]!
        let (normalized, equality) ← normalizeSourceData entry
        let tail ← mkFreshExprMVar (← mkAppM ``SourceListCertificate #[rest])
        goal.assign (← withTransparency .all <| mkAppM ``SourceListCertificate.cons
          #[entry, normalized, ← mkEqSymm equality, tail])
        goal := tail.mvarId!
        currentSource := rest
        count := count + 1
        continue
      let (newSource, equality?) ← sourceReductionStep reduced
      if let some equality := equality? then
        let next ← mkFreshExprMVar (← mkAppM ``SourceListCertificate #[newSource])
        goal.assign (← mkAppM ``SourceListCertificate.transport #[← mkEqSymm equality, next])
        goal := next.mvarId!
      currentSource := newSource
    throwError "source-list certificate step limit reached"

end Zcash.Meta
