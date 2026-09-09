import Zcash.Meta.SourceReduction
import Zcash.Meta.CertificateChunks
import Zcash.Snark.ZeroKnowledge.AdviceSourceCertificate

/-!
# Source-preserving annotation certificates

This elaborator exposes the original operation list by definitional reduction
and the source's own opaque-value equations. It then attaches a semantic support
proof to each tagged instruction. Transport retains the exact annotation data.
The completed source certificate is checked synchronously by Lean's kernel.
Neither a successful alias scan nor a successful read scan is inferred here.
-/

namespace Zcash.Meta

open Lean Meta Elab Tactic
open Halo2 Witgen Zcash.Circuits Zcash.Snark.ZeroKnowledge SourceReduction

initialize registerTraceClass `Zcash.adviceSourceCertificate

private def nilFpCertificate : AdviceSourceCertificate ([] : List (PlacedAdviceProgram Fp × Option AdviceAddress)) :=
  AdviceSourceCertificate.nil

private def sourceCertificateProgress (message : String) : MetaM Unit := do
  if ← isTracingEnabledFor `Zcash.adviceSourceCertificate then
    IO.eprintln s!"[advice certificate] {message}"

private def transportCertificateSource (goal : MVarId) (source equality : Expr) : MetaM MVarId := do
  let target ← mkAppM ``AdviceSourceCertificate #[source]
  let next ← mkFreshExprMVar target
  let reverse ← mkEqSymm equality
  goal.assign (← mkAppM ``AdviceSourceCertificate.transport #[reverse, next])
  return next.mvarId!

/-- Annotate the original source, opening opaque source barriers only by their proved equations. -/
elab "certify_source_advice" : tactic =>
  withOptions (fun options => options.setBool `smartUnfolding false) <| withMainContext do
    let originalGoal ← getMainGoal
    let originalTarget ← originalGoal.getType
    unless originalTarget.isAppOf ``AdviceSourceCertificate do
      throwError "expected an AdviceSourceCertificate goal"
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
      if step % 1000 == 0 then sourceCertificateProgress s!"step {step}: {count} annotated instructions"
      if step > 0 && step % chunkSteps == 0 then
        let nextTarget ← instantiateMVars (← goal.getType)
        chunks := chunks.push (← checkCertificateChunk first.mvarId! goal compilePieces)
        if nextTarget.hasMVar || chunks.back!.hasMVar then
          throwError "unresolved advice chunk boundary"
        setMCtx savedMCtx
        resetCache
        first ← mkFreshExprMVar nextTarget
        goal := first.mvarId!
      let reduced ← withTransparency .all (whnf currentSource)
      if reduced.isAppOf ``List.nil then
        goal.assign (mkConst ``nilFpCertificate)
        let mut value ← checkCertificateValue first.mvarId! compilePieces
        for chunk in chunks.reverse do value := mkApp chunk value
        originalGoal.assign value
        sourceCertificateProgress s!"kernel checked {count} original instructions"
        replaceMainGoal []
        return
      if reduced.isAppOf ``List.cons then
        let arguments := reduced.getAppArgs
        let instruction := arguments[1]!
        let rest := arguments[2]!
        let (reads, support) ← annotateAdviceInstruction (← mkAppM ``Prod.fst #[instruction])
        let data ← mkAppM ``adviceSourceEntryData #[instruction, reads]
        let (normalized, equality) ← normalizeSourceData data
        let tailType ← mkAppM ``AdviceSourceCertificate #[rest]
        let tail ← mkFreshExprMVar tailType
        let value ← withTransparency .all <| mkAppM ``AdviceSourceCertificate.consWithData
          #[instruction, reads, support, normalized, ← mkEqSymm equality, tail]
        goal.assign value
        goal := tail.mvarId!
        currentSource := rest
        count := count + 1
        continue
      currentSource := reduced
      let (newSource, equality?) ← sourceReductionStep reduced
      if let some equality := equality? then
        goal ← transportCertificateSource goal newSource equality
      currentSource := newSource
    throwError "source certificate step limit reached"


end Zcash.Meta
