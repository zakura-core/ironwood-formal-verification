import Zcash.Snark.ZeroKnowledge.NativeScalarWitnessSupport
import Zcash.Snark.ZeroKnowledge.PoseidonWitnessSupport
import Zcash.Snark.ZeroKnowledge.MulIncompleteWitnessSupport
import Zcash.Snark.ZeroKnowledge.FixedBaseWitnessSupport
import Zcash.Snark.ZeroKnowledge.FixedCanonicityWitnessSupport
import Zcash.Snark.ZeroKnowledge.NoteWitnessSupport
import Zcash.Snark.ZeroKnowledge.NoteCanonicityWitnessSupport
import Zcash.Snark.ZeroKnowledge.CommitIvkWitnessSupport
import Zcash.Snark.ZeroKnowledge.SinsemillaWitnessSupport
import Zcash.Snark.ZeroKnowledge.MerkleWitnessSupport
import Zcash.Snark.ZeroKnowledge.ActionHintReadSupport
import Zcash.Snark.ZeroKnowledge.AdviceSupportPlan

/-!
# Producing semantic read annotations for the original Action helpers

The elaborator applies the declared support theorems and recursively discharges
nested support premises. All generated annotations retain their original program
and carry a kernel-checked proof. Rule search is bounded and an unsupported
callback is rejected; no native evaluator supplies a logical certificate.
-/

namespace Zcash.Meta

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Lean Meta Elab Tactic
open Halo2 Witgen Zcash.Circuits Zcash.Snark.ZeroKnowledge

private theorem scalarSupport (program : MOver Fp (AssignedCell Fp) (FExpr Fp)) :
    WitnessFunctionSupport (valueBuilderReads (value := field) program)
      (fun env => ((program.toIRScalar (Env := Placed ProverEnvironment Fp)).eval env)[0]) := by
  intro left right agreement
  dsimp only
  simp only [MOver.eval_toIRScalar]
  exact valueBuilderReads_eval (value := field) program left right agreement

private theorem structuredSupport (steps : List (StepOver Fp (AssignedCell Fp)))
    (output : VExprOver Fp (AssignedCell Fp) 1) :
    WitnessFunctionSupport (stepsWitnessReads steps ++ vectorWitnessReads output)
      (fun env => ((.ir steps output : WitgenIR Fp 1).eval env)[0]) :=
  (supportedStructuredAdvice ⟨0⟩ 0 steps output).support

private theorem fieldExpressionSupport (expression : FExpr Fp) :
    WitnessFunctionSupport (fieldWitnessReads expression)
      (fun env => ((WitgenIROver.ofFExpr expression : WitgenIR Fp 1).eval env)[0]) := by
  intro left right agreement
  dsimp only
  rw [eval_ofFExpr_zero, eval_ofFExpr_zero]
  exact fieldWitnessReads_eval expression { env := left } { env := right } agreement

private def supportRules : Array Name := #[
  ``scalarSupport, ``structuredSupport, ``fieldExpressionSupport,
  ``witnessFunctionSupport_readCell,
  ``witnessFunctionSupport_valueBuilder, ``witnessFunctionSupport_natBuilder,
  ``witnessFunctionSupport_boolBuilder,
  ``mulIncomplete_stepWit_baseX_support,
  ``mulIncomplete_stepWit_baseY_support,
  ``nativeConstant_support,
  ``nativeBoolean_support,
  ``addChip_sumWit_support,
  ``poseidon_constWit_support,
  ``poseidon_addWit_support,
  ``poseidon_readCellWit_support,
  ``poseidon_rowWit_support,
  ``mulIncomplete_readsValue_support,
  ``mulIncomplete_readWit_support,
  ``mulIncomplete_stepWit_support,
  ``mulIncomplete_initLambdaWit_support,
  ``mulFixed_windowVal_support,
  ``mulFixed_xPWit_support,
  ``mulFixed_yPWit_support,
  ``mulFixed_uWit_support,
  ``mulFixed_hintWindowVal_support,
  ``mulFixed_xPWitH_support,
  ``mulFixed_yPWitH_support,
  ``mulFixed_uWitH_support,
  ``mulFixed_alphaZeroPrimeWit_support,
  ``mulFixed_alpha1Wit_support,
  ``mulFixed_alpha2Wit_support,
  ``mulFixed_yVarWit_support,
  ``note_brWit_support,
  ``note_bWit_support,
  ``note_dWit_support,
  ``note_eWit_support,
  ``note_gWit_support,
  ``note_hWit_support,
  ``note_aPrimeWit_support,
  ``note_b3CPrimeWit_support,
  ``note_e1FPrimeWit_support,
  ``note_g1G2PrimeWit_support,
  ``note_k0Wit_support,
  ``note_k2Wit_support,
  ``note_k3Wit_support,
  ``note_jPrimeWit_support,
  ``note_jWit_support,
  ``commitIvk_bWit_support,
  ``commitIvk_dWit_support,
  ``commitIvk_aPrimeWit_support,
  ``commitIvk_b2CPrimeWit_support,
  ``sinsemilla_readsValue_support,
  ``sinsemilla_initXPWit_support,
  ``sinsemilla_zWit_support,
  ``sinsemilla_stepWit_support,
  ``sinsemilla_exitXAWit_support,
  ``sinsemilla_initLWit_support,
  ``sinsemilla_boundaryYA_support,
  ``sinsemilla_finalYAWit_support,
  ``sinsemilla_zeroWit_support,
  ``sinsemilla_constWit_support,
  ``merkle_waWit_support,
  ``merkle_wb1Wit_support,
  ``merkle_wb2Wit_support,
  ``merkle_wbWit_support,
  ``merkle_wcWit_support,
  ``actionMerkleSiblingHint_support,
  ``actionMerkleSwapHint_support,
  ``witnessFunctionSupport_const
]

private partial def closeReadSupport (goal : MVarId) (fuel : Nat) : MetaM Unit := do
  if fuel == 0 then throwError "read support recursion exhausted"
  for name in supportRules do
    let saved ← saveState
    try
      let rule ← mkConstWithFreshMVarLevels name
      let mut arguments : Array Expr := #[]
      let mut conclusion ← inferType rule
      while conclusion.isForall do
        let argument ← mkFreshExprMVar conclusion.bindingDomain!
        arguments := arguments.push argument
        conclusion := conclusion.bindingBody!.instantiate1 argument
      let transparency := if name == ``witnessFunctionSupport_const ||
          name == ``sinsemilla_boundaryYA_support then TransparencyMode.default else .reducible
      unless ← withTransparency transparency (isDefEq conclusion (← goal.getType)) do
        throwError "source rule does not match"
      for argument in arguments do
        let argument ← instantiateMVars argument
        if argument.isMVar && (← isProp (← inferType argument)) then
          closeReadSupport argument.mvarId! (fuel - 1)
      let certificate ← instantiateMVars (mkAppN rule arguments)
      if certificate.hasMVar then throwError "unresolved source rule arguments"
      goal.assign certificate
      return
    catch _ => saved.restore
  throwError "no support certificate for {← goal.getType}"

elab "witness_read_support" : tactic => withMainContext do
  let goal ← getMainGoal
  closeReadSupport goal 16
  replaceMainGoal []

elab "annotate_advice " instruction:term : term => do
  let constructor ← Term.elabTerm (← `(supportedAdviceProgram $instruction)) none
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constructor)
  unless arguments.size == 2 do throwError "expected reads and support"
  closeReadSupport arguments[1]!.mvarId! 16
  let annotated ← instantiateMVars (mkAppN constructor arguments)
  if annotated.hasMVar then throwError "annotation contains unresolved metavariables"
  return annotated


/-- Produce the read list and its proof for the exact supplied instruction. -/
def annotateAdviceInstruction (instruction : Expr) : MetaM (Expr × Expr) := do
  -- Structured IR is certified compositionally, including named wrappers.
  -- Native closures still need a rule about their actual source function.
  let program ← mkAppM ``PlacedAdviceProgram.program #[instruction]
  let reduced ← withTransparency .all (whnf program)
  if reduced.isAppOf ``WitgenIROver.ir then
    let values := reduced.getAppArgs
    let steps := values[values.size - 2]!
    let output := values.back!
    let column ← mkAppM ``PlacedAdviceProgram.column #[instruction]
    let row ← mkAppM ``PlacedAdviceProgram.row #[instruction]
    let annotated ← mkAppM ``supportedStructuredAdvice #[column, row, steps, output]
    return (← mkAppM ``SupportedAdviceProgram.reads #[annotated],
      ← mkAppM ``SupportedAdviceProgram.support #[annotated])
  let constructor ← mkAppM ``supportedAdviceProgram #[instruction]
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constructor)
  unless arguments.size == 2 do throwError "expected reads and support"
  closeReadSupport arguments[1]!.mvarId! 16
  let reads ← instantiateMVars arguments[0]!
  let support ← instantiateMVars arguments[1]!
  if reads.hasMVar || support.hasMVar then throwError "unresolved annotation"
  return (reads, support)


end Zcash.Meta
