import Zcash.Snark.ZeroKnowledge.StoredActionTapeTraceCost
import Zcash.Snark.ZeroKnowledge.StoredActionJointSize

/-! # A fixed complete bit-to-transcript envelope for the original Action simulator -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Complete tape, joint simulation, proof preparation, and transcript construction cost. -/
def storedActionTapeTraceCostBudget (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess actions bitLength : ℕ) (key : StoredPlonkKey) : ℕ :=
  let challengeRead := plonkStoredTapeReadBudget actions 11 read
  let rowRead := storedActionJointInputBudget actions 0 read
  let access := routedProofReadBudget actions (22 * actions) equal read
    (storedJointProofInputBudget fieldCosts read omegaAccess rowRead challengeRead (22 * actions + 10) 11)
  let preparation := 3 * (22 * actions) + read +
    4 * (privateOpeningEvaluationCostBudget fieldCosts equal read actions (22 * actions) (read + 11) challengeRead + 1) + 65
  storedActionTapeJointCostBudget fieldCosts ipaCosts node equal read omegaAccess actions bitLength key +
    preparation + 8 * actions * actions + (72 * actions + 85) * access + 1300 * actions + 2200

set_option maxRecDepth 10000 in
/-- Every complete input bit tape obeys the same concrete polynomial transcript-production envelope. -/
theorem storedActionTapeTraceCosted_cost_le_fixed
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (bits : Fin ((22 + plonkSimulatorSampleCount inputs.length 11) * 512) → Bool) :
    (storedActionTapeTraceCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (List.ofFn bits)).2 ≤
      storedActionTapeTraceCostBudget fieldCosts ipaCosts node equal read omegaAccess inputs.length
        ((22 + plonkSimulatorSampleCount inputs.length 11) * 512) (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let joint := storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs
    setup (StoredPlonkKey.encode vk) (List.ofFn bits)
  let access := plonkStoredTapeReadBudget inputs.length 11 read
  let rowRead := storedActionJointInputBudget inputs.length 0 read
  have hshape := storedActionTapeJointCosted_shape fieldCosts ipaCosts node equal read omegaAccess
    inputs generators W U fixed sigma vk bits
  have hinstances (action : Fin inputs.length) (row : Fin 2048) :
      (actionStoredInstanceRowCosted read inputs action row).2 ≤ rowRead := by
    have h := actionStoredInstanceRowCosted_cost_le read inputs action row
    dsimp only [rowRead, storedActionJointInputBudget]
    omega
  have hfixed (column : Fin 29) (row : Fin 2048) : (setup.fixedCosted read column row).2 ≤ rowRead := by
    have h := StoredPlonkSetup.fixedCosted_encode_cost_le generators W U fixed sigma read column row
    dsimp only [rowRead, storedActionJointInputBudget]
    exact h.trans (by omega)
  have hsigma (column : Fin 15) (row : Fin 2048) : (setup.sigmaCosted read column row).2 ≤ rowRead := by
    have h := StoredPlonkSetup.sigmaCosted_encode_cost_le generators W U fixed sigma read column row
    dsimp only [rowRead, storedActionJointInputBudget]
    exact h.trans (by omega)
  have hrows : ∀ row ∈ joint.1.joint.1.2.1, row.length ≤ 5 :=
    fun row hrow => (hshape.2.2.1 row hrow).le
  have ht := storedJointTraceCosted_cost_le (k := 11) fieldCosts equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint
    rowRead hinstances hfixed hsigma hrows
  dsimp only at ht
  rw [hshape.1, hshape.2.1, hshape.2.2.2] at ht
  have hj := storedActionTapeJointCosted_cost_le_fixed fieldCosts ipaCosts node equal read omegaAccess
    inputs generators W U fixed sigma (StoredPlonkKey.encode vk) (List.ofFn bits)
  rw [List.length_ofFn] at hj
  change joint.2 ≤ _ at hj
  change joint.2 + (storedJointTraceCosted (k := 11) fieldCosts equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint).2 + 3 ≤ _
  dsimp only [storedActionTapeTraceCostBudget, access, rowRead] at ht ⊢
  rw [show 72 * inputs.length + 2 * 11 + 63 = 72 * inputs.length + 85 by omega] at ht
  omega

end Zcash.Snark.ZeroKnowledge
