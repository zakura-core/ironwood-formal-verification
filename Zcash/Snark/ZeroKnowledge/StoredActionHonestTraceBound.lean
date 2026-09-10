import Zcash.Snark.ZeroKnowledge.StoredActionHonestTraceCost
import Zcash.Snark.ZeroKnowledge.StoredActionJointSize

/-! # A fixed complete bit-to-transcript envelope for the original real Action prover -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Complete tape, joint proof construction, proof preparation, and transcript construction cost. -/
def storedActionHonestTraceCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions bitLength : ℕ) (key : StoredPlonkKey) : ℕ :=
  let challengeRead := storedPlonkProverTapeReadBudget actions read
  let rowRead := storedActionJointInputBudget actions 0 read
  let access := routedProofReadBudget actions (22 * actions) equal read
    (storedJointProofInputBudget costs read omegaAccess rowRead challengeRead (22 * actions + 10) 11)
  let preparation := 3 * (22 * actions) + read +
    4 * (privateOpeningEvaluationCostBudget costs equal read actions (22 * actions) (read + 11) challengeRead + 1) + 65
  storedActionHonestTapeJointCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale actions bitLength key +
    preparation + 8 * actions * actions + (72 * actions + 85) * access + 1300 * actions + 2200

set_option maxRecDepth 10000 in
/-- Every complete input bit tape obeys the same concrete polynomial transcript-production envelope. -/
theorem storedActionHonestTraceCosted_cost_le_fixed
    (costs : FieldOperationCosts) (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (bits : List Bool) :
    (storedActionHonestTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (encodeActionWitness witness) bits).2 ≤
      storedActionHonestTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs.length
        bits.length (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let joint := storedActionHonestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
    setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) bits
  let access := storedPlonkProverTapeReadBudget inputs.length read
  let rowRead := storedActionJointInputBudget inputs.length 0 read
  have hshape := storedActionHonestTapeJointCosted_shape costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) bits
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
  have ht := storedJointTraceCosted_cost_le (k := 11) costs equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint
    rowRead hinstances hfixed hsigma hrows
  dsimp only at ht
  rw [hshape.1, hshape.2.1, hshape.2.2.2] at ht
  have hj := storedActionHonestTapeJointCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma (StoredPlonkKey.encode vk) witness bits
  change joint.2 ≤ _ at hj
  unfold storedActionHonestTraceCosted
  change joint.2 + (storedJointTraceCosted (k := 11) costs equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint).2 + 3 ≤ _
  dsimp only [storedActionHonestTraceCostBudget, access, rowRead] at ht ⊢
  rw [show 72 * inputs.length + 2 * 11 + 63 = 72 * inputs.length + 85 by omega] at ht
  omega

end Zcash.Snark.ZeroKnowledge
