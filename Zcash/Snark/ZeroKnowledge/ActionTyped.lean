import Zcash.Snark.ZeroKnowledge.ActionInstantiation

/-!
# The complete typed Action view for oracle observations

This is the same reference computation and public simulator before encoding and
abort observation. Exposing its already proved comparison allows a subsequent
observation to construct the affine-coordinate hash inputs and raw oracle view.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common

/-- Keep the entire typed reference proof and independent verifier tape. -/
noncomputable def actionZkTypedProver {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    PMF (PlonkFreshView actions urs.k VestaG) :=
  let vk := actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen
  let pub := actionPublicPolynomials inputs
  freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k) (plonkTotalColumnConstructor vk pub witness) [] vk pub

/-- Keep the corresponding full typed view of the witness-free simulator. -/
noncomputable def actionZkTypedSimulator [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp) :
    PMF (PlonkFreshView actions urs.k VestaG) :=
  freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k)
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs)

/-- The typed Action comparison has the same closed compiler assumptions and numerical error. -/
theorem wideActionZkTyped_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0) :
    PMFEventBiasLE (actionZkTypedProver urs hk inputs witness) (actionZkTypedSimulator urs hk inputs)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE (actionZkTypedSimulator urs hk inputs) (actionZkTypedProver urs hk inputs witness)
        (plonkSimulationErrorBound actions) :=
  wideActionCompilerTypedReference_simulation_error_bound urs hk inputs witness hvalid.rows hW hvalid.copies

/-- The canonical attempt observer recovers the existing encoded reference experiment exactly. -/
theorem actionZkTypedProver_encoded [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    (actionZkTypedProver urs hk inputs witness).map encodedPlonkAttempt = actionZkProver urs hk inputs witness :=
  (freshEncodedPlonkReferenceAttempt_law urs hk _ _ witness).symm

/-- The same canonical observation recovers the existing encoded simulator exactly. -/
theorem actionZkTypedSimulator_encoded [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp) :
    (actionZkTypedSimulator urs hk inputs).map encodedPlonkAttempt = actionZkSimulator urs hk inputs := rfl

end Zcash.Snark.ZeroKnowledge
