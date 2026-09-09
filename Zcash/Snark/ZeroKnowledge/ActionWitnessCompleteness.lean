import Zcash.Snark.ZeroKnowledge.ActionWitnessExtraction

/-!
# Applying the original Action completeness theorem to generated rows

The checked application conditions transfer through the exact private readings
and preserved public inputs to the existing top-level completeness theorem. The
remaining premise is the original witness-equation predicate, which the source
certificate must discharge independently. The conclusion here is the original
operation constraints; the compiler's converse gate, lookup, and copy bridges
are separate obligations for the complete PLONK row relation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

/-- The original Action completeness theorem accepts the exact application readings. -/
theorem actionWitnessAssignment_constraints_of_readAgreement
    (inputs : PublicInputs Fp) (witness : PrivateWitness)
    (conditions : ActionWitnessConstructionConditions inputs witness)
    (hw : ExtendsWitnesses actionCircuit.placement
      (actionCircuit.proverEnvironment (actionWitnessAssignment inputs witness) (actionWitnessHints witness))
      actionCircuit.operations 0)
    (agreement : ActionWitnessReadAgreement
      (PrivateWitness.ofActionData (Circuit.extractPost actionConfig () 0
        (actionCircuit.placedEnvironment (actionWitnessAssignment inputs witness))))
      (normalizeActionWitness witness)) :
    Constraints actionCircuit.placement
      (actionCircuit.environment (actionWitnessAssignment inputs witness)) actionCircuit.operations 0 := by
  let data := Circuit.extractPost actionConfig () 0
    (actionCircuit.placedEnvironment (actionWitnessAssignment inputs witness))
  have hpublic : PublicInputs.ofActionData data = inputs := by
    dsimp only [data]
    rw [PublicInputs.ofActionData_extractPost _ _ _ (by rfl)]
    have h := actionWitnessAssignment_publicInput inputs witness
    have hlayout (environment : Environment Fp) :
        actionCircuit.publicInputLayout.extract environment = PublicInputs.layout.extract environment := by
      rw [Internal.actionCircuit_eq_impl]
      rfl
    rw [hlayout] at h
    exact h
  have hparts : combine inputs (PrivateWitness.ofActionData data) = data := by
    rw [← hpublic]
    exact combine_parts data
  have hpre := actionWitnessConditions_proverAssumptions_of_readAgreement
    conditions (PrivateWitness.ofActionData data) agreement (actionWitnessHints witness)
  rw [hparts] at hpre
  apply (actionCircuit.completeness (actionWitnessAssignment inputs witness)
    (actionWitnessHints witness) hw ?_).1
  have hformal : actionCircuit.formalCircuit =
      Circuit.circuit Specs.Sinsemilla.orchardGenerators orchardBases := by
    rw [Internal.actionCircuit_eq_impl]
    rfl
  have hconfig : actionCircuit.config = actionConfig := by
    rw [Internal.actionCircuit_eq_impl]
    rfl
  rw [hformal, hconfig]
  exact hpre

/-- The generated assignment satisfies the original operation constraints once its witness equations hold. -/
theorem actionWitnessAssignment_constraints_of_extendsWitnesses
    (inputs : PublicInputs Fp) (witness : PrivateWitness)
    (conditions : ActionWitnessConstructionConditions inputs witness)
    (hw : ExtendsWitnesses actionCircuit.placement
      (actionCircuit.proverEnvironment (actionWitnessAssignment inputs witness) (actionWitnessHints witness))
      actionCircuit.operations 0) :
    Constraints actionCircuit.placement
      (actionCircuit.environment (actionWitnessAssignment inputs witness)) actionCircuit.operations 0 :=
  actionWitnessAssignment_constraints_of_readAgreement inputs witness conditions hw
    (actionWitnessAssignment_readAgreement_of_extendsWitnesses inputs witness conditions.scalarHints hw)

end Zcash.Snark.ZeroKnowledge
