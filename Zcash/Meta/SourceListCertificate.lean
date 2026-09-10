import Zcash.Meta.SourceReduction
import Zcash.Meta.CertificateChunks
import Zcash.Snark.ZeroKnowledge.SourceListCertificate
import Zcash.Snark.ZeroKnowledge.SourceCertificatePiece

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

/-- Reflect a bounded prefix while retaining the exact unprocessed source.
Separate declarations compose these checked continuations with a certificate
for the final remainder. -/
elab "certify_source_list_piece " steps:num entries:num : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let originalGoal ← getMainGoal
    let target ← originalGoal.getType
    unless target.isAppOf ``SourceCertificatePiece do
      throwError "expected a SourceCertificatePiece goal"
    let arguments := target.getAppArgs
    let family := arguments[arguments.size - 2]!
    let source := arguments.back!
    let first ← mkFreshExprMVar (mkApp family source)
    let mut goal := first.mvarId!
    let mut currentSource := source
    let mut count := 0
    let compilePieces := !(← readThe Term.Context).isNoncomputableSection &&
      !(← Term.getDeclName?).any (Lean.isNoncomputable (← getEnv))
    for _ in [:steps.getNat] do
      if count == entries.getNat then break
      let reduced ← withTransparency .all (whnf currentSource)
      if reduced.isAppOf ``List.nil then
        currentSource := reduced
        break
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
      else
        let (newSource, equality?) ← sourceReductionStep reduced
        if let some equality := equality? then
          let next ← mkFreshExprMVar (← mkAppM ``SourceListCertificate #[newSource])
          goal.assign (← mkAppM ``SourceListCertificate.transport #[← mkEqSymm equality, next])
          goal := next.mvarId!
        currentSource := newSource
    let continuation ← checkCertificateChunk first.mvarId! goal compilePieces
    originalGoal.assign (← mkAppM ``SourceCertificatePiece.mk #[currentSource, continuation])
    listCertificateProgress s!"{← Term.getDeclName?}: checked {count} entries; remainder empty: {currentSource.isAppOf ``List.nil}"
    replaceMainGoal []

/-- Certify the exact list produced by a source projection, using only checked equalities. -/
elab "certify_source_list" : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let originalGoal ← getMainGoal
    let originalTarget ← originalGoal.getType
    unless originalTarget.isAppOf ``SourceListCertificate do
      throwError "expected a SourceListCertificate goal"
    let elementType := originalTarget.getAppArgs[0]!
    let savedMCtx ← getMCtx
    let compilePieces := !(← readThe Term.Context).isNoncomputableSection &&
      !(← Term.getDeclName?).any (Lean.isNoncomputable (← getEnv))
    let mut first ← mkFreshExprMVar originalTarget
    let mut goal := first.mvarId!
    let mut chunks : Array Expr := #[]
    let chunkSteps := max 1 (Zcash.sourceCertificate.chunkSteps.get (← getOptions))
    let mut currentSource := originalTarget.getAppArgs.back!
    let mut count := 0
    for step in [:200000] do
      if step % 1000 == 0 then listCertificateProgress s!"step {step}: {count} entries"
      if step > 0 && step % chunkSteps == 0 then
        let nextTarget ← instantiateMVars (← goal.getType)
        chunks := chunks.push (← checkCertificateChunk first.mvarId! goal compilePieces)
        if nextTarget.hasMVar || chunks.back!.hasMVar then
          throwError "unresolved source-list chunk boundary"
        setMCtx savedMCtx
        resetCache
        first ← mkFreshExprMVar nextTarget
        goal := first.mvarId!
      let reduced ← withTransparency .all (whnf currentSource)
      if reduced.isAppOf ``List.nil then
        goal.assign (← mkAppOptM ``SourceListCertificate.nil #[some elementType])
        let mut value ← checkCertificateValue first.mvarId! compilePieces
        for chunk in chunks.reverse do value := mkApp chunk value
        originalGoal.assign value
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
