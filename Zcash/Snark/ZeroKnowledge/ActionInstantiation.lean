import Zcash.Snark.ZeroKnowledge.ActionCompilerSimulation
import Zcash.Snark.ZeroKnowledge.CapturedBlinding

/-!
# The Action validity relation and a captured-setup instantiation

`ActionZkRelation` packages the original gate, lookup, and compiler copy equations
of the proved circuit relation. It does not assume a successful proof attempt.
The simulator depends only on the setup and public input.

The captured-setup corollary uses the one-Action honest fixture's eleven-round URS,
for any Action count. Its blinding point has the existing kernel-checked
nonidentity certificate. This specializes captured public parameters; it does not
assert a parameter-generation algorithm or an `ActionSpec` witness constructor.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common

/-- Original satisfying rows and the complete concrete compiler copy equations. -/
structure ActionZkRelation {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) : Prop where
  rows : PlonkOriginalRowsValid
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs) witness
  copies :
    let vk := actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen
    let pub := actionPublicPolynomials inputs
    let pairs := plonkKeygenCopies actionCircuit actionCircuit_permutationColumnCount_eq
      (actionCircuit_operations_usedRows_eq_1779.le.trans (by decide)) vk.permutationChunks
      (actionReferenceKey_copyChunkWidths (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    ∀ a : Fin actions, ∀ pair ∈ pairs,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1

/-- The complete encoded Action reference attempt on independent wide-reduced tapes. -/
noncomputable def actionZkProver {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    PMF (Challenges urs.k Fp × ProverAttemptResult) :=
  freshEncodedPlonkReferenceAttempt urs hk
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs) witness

/-- The same encoded observation of the witness-free public Action simulator. -/
noncomputable def actionZkSimulator [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp) :
    PMF (Challenges urs.k Fp × ProverAttemptResult) :=
  (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k)
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs)).map encodedPlonkAttempt

/-- A single validity relation supplies all witness premises of the concrete simulation theorem. -/
theorem wideActionZkRelation_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0) :
    PMFEventBiasLE (actionZkProver urs hk inputs witness) (actionZkSimulator urs hk inputs)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE (actionZkSimulator urs hk inputs) (actionZkProver urs hk inputs witness)
        (plonkSimulationErrorBound actions) :=
  wideActionCompilerReference_simulation_error_bound urs hk inputs witness hvalid.rows hW hvalid.copies

/-- The named URS captured by the checked-in one-Action honest fixture. -/
def capturedActionURS : URS VestaG := Fixture.capturedURS

/-- The captured setup has the eleven rounds required by the reference prover. -/
theorem capturedActionURS_rounds : capturedActionURS.k = 11 := rfl

/-- The captured setup discharges the blinding-point premise by its existing coordinate certificate. -/
theorem capturedActionURS_blinding_ne_zero : capturedActionURS.w ≠ 0 :=
  CapturedBlinding.singleActionHonest_w_ne_zero

/-- The captured setup and one validity relation instantiate the entire encoded Action comparison. -/
theorem wideCapturedActionZk_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation capturedActionURS capturedActionURS_rounds inputs witness) :
    PMFEventBiasLE (actionZkProver capturedActionURS capturedActionURS_rounds inputs witness)
        (actionZkSimulator capturedActionURS capturedActionURS_rounds inputs)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE (actionZkSimulator capturedActionURS capturedActionURS_rounds inputs)
        (actionZkProver capturedActionURS capturedActionURS_rounds inputs witness)
        (plonkSimulationErrorBound actions) :=
  wideActionZkRelation_simulation_error_bound capturedActionURS capturedActionURS_rounds inputs witness
    hvalid capturedActionURS_blinding_ne_zero

end Zcash.Snark.ZeroKnowledge
