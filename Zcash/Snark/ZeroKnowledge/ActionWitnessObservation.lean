import Zcash.Snark.ZeroKnowledge.ActionWitnessConditions

/-!
# The finite observations needed from an extracted Action witness

The original extractor gives its auxiliary Merkle readings as a function on
natural numbers. Only the first 32 readings occur in the two 16-layer honest
computations. Agreement with the application constructor therefore retains all
witness fields and those 32 readings, without requiring unused tail values to
equal the constructor's zero padding.

The theorems below preserve the existing specification and honest-prover
preconditions exactly. They do not assume or prove that the actual extractor
already agrees with the constructed witness.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Circuits.Sinsemilla.Merkle.CalculateRoot

/-- Retain every witness field and exactly the 32 auxiliary Merkle readings used by the Action. -/
def actionWitnessObservation (witness : PrivateWitness) : PrivateWitness :=
  { witness with merklePath := fun index =>
      if index < 32 then witness.merklePath index else (0, 0) }

/-- Observation leaves every used Merkle reading unchanged. -/
theorem actionWitnessObservation_merklePath (witness : PrivateWitness) (index : ℕ)
    (hindex : index < 32) :
    (actionWitnessObservation witness).merklePath index = witness.merklePath index := by
  simp only [actionWitnessObservation, if_pos hindex]

/-- The original first half reads only retained entries. -/
theorem actionWitnessObservation_firstHalf (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (witness : PrivateWitness) (node : Fp) :
    pathNode generators point 0 (actionWitnessObservation witness).merklePath node 16 =
      pathNode generators point 0 witness.merklePath node 16 := by
  apply pathNode_congr
  intro index hindex
  exact actionWitnessObservation_merklePath witness index (by omega)

/-- The original second half reads precisely entries 16 through 31. -/
theorem actionWitnessObservation_secondHalf (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (witness : PrivateWitness) (node : Fp) :
    pathNode generators point 16
        (fun index => (actionWitnessObservation witness).merklePath (16 + index)) node 16 =
      pathNode generators point 16 (fun index => witness.merklePath (16 + index)) node 16 := by
  apply pathNode_congr
  intro index hindex
  exact actionWitnessObservation_merklePath witness (16 + index) (by omega)

/-- Truncating the unused auxiliary tail preserves the complete application specification. -/
theorem actionWitnessObservation_spec_iff (inputs : PublicInputs Fp) (witness : PrivateWitness) :
    ActionSpec inputs (actionWitnessObservation witness) ↔ ActionSpec inputs witness := by
  rfl

/-- The original honest-prover preconditions depend only on the retained observations. -/
theorem actionWitnessObservation_proverAssumptions_iff
    (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (inputs : PublicInputs Fp) (witness : PrivateWitness) (hints : ProverHint Fp) :
    Circuit.ProverAssumptionsPost generators bases ()
        (combine inputs (actionWitnessObservation witness)) hints ↔
      Circuit.ProverAssumptionsPost generators bases () (combine inputs witness) hints := by
  have first := actionWitnessObservation_firstHalf generators bases.merkleQ witness witness.cmOld.x
  have second := actionWitnessObservation_secondHalf generators bases.merkleQ witness
  simp only [Circuit.ProverAssumptionsPost, Circuit.ProverAssumptions,
    Circuit.ProverAssumptionsCore, combine, actionWitnessObservation] at first second ⊢
  rw [first]
  simp only [second]

/-- Application normalization already pads exactly the unused Merkle tail. -/
theorem actionWitnessObservation_normalize (witness : PrivateWitness) :
    actionWitnessObservation (normalizeActionWitness witness) = normalizeActionWitness witness := by
  have hpath : (fun index => if index < 32 then canonicalActionMerklePath witness index else (0, 0)) =
      canonicalActionMerklePath witness := by
    funext index
    by_cases hindex : index < 32 <;>
      simp [canonicalActionMerklePath, hindex]
  simp only [actionWitnessObservation, normalizeActionWitness, hpath]

/-- Agreement on actual Action observations transfers the constructor's preconditions to the extracted data. -/
theorem actionWitnessConditions_proverAssumptions_of_observation
    {inputs : PublicInputs Fp} {witness : PrivateWitness}
    (conditions : ActionWitnessConstructionConditions inputs witness)
    (extracted : PrivateWitness)
    (hagreement : actionWitnessObservation extracted = normalizeActionWitness witness)
    (hints : ProverHint Fp) :
    Circuit.ProverAssumptionsPost Specs.Sinsemilla.orchardGenerators orchardBases ()
      (combine inputs extracted) hints := by
  apply (actionWitnessObservation_proverAssumptions_iff _ _ inputs extracted hints).mp
  rw [hagreement]
  exact actionWitnessConditions_proverAssumptions conditions hints

end Zcash.Snark.ZeroKnowledge
