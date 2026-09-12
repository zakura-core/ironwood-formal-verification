import Zcash.Snark.ZeroKnowledge.StoredActionHonestTapeJoint

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Fixed complete real Action joint-prover budget, independent of all sampled bit values. -/
def storedActionHonestTapeJointCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions bitLength : ℕ)
    (key : StoredPlonkKey) : ℕ :=
  storedPlonkProverTapeCostBudget actions read bitLength +
    honestTapeJointCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale actions
      (fieldSampleCount actions) (storedActionHonestInputBudget actions (storedPlonkProverTapeReadBudget actions read) read)
      key (storedPlonkChallengePriceModel 11 read) + 3

/-- Tape construction and concrete input readers discharge the full fixed-bit real-prover runtime envelope. -/
theorem storedActionHonestTapeJointCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) (key : StoredPlonkKey)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (bits : List Bool) :
    (storedActionHonestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) key (encodeActionWitness witness) bits).2 ≤
      storedActionHonestTapeJointCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length bits.length key := by
  let tapes := storedPlonkProverTapesCosted inputs.length read bits
  have ht := storedPlonkProverTapesCosted_cost_le inputs.length read bits
  have hc := storedPlonkProverTapesCosted_readBound inputs.length read bits
  have hj := storedActionHonestJointCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma key witness tapes.1.challenges tapes.1.privateFields
    (storedPlonkProverTapeReadBudget inputs.length read) hc
  have hl : tapes.1.privateFields.length = fieldSampleCount inputs.length :=
    (storedPlonkProverTapesCosted_lengths inputs.length read bits).2
  rewrite [hl] at hj
  have hp := honestTapeJointCostBudget_congr_prices costs node equal read omegaAccess canonicalRead compare
    groupAdd groupScale inputs.length (fieldSampleCount inputs.length)
    (storedActionHonestInputBudget inputs.length (storedPlonkProverTapeReadBudget inputs.length read) read)
    key tapes.1.challenges (storedPlonkChallengePriceModel 11 read)
    (storedPlonkProverTapesCosted_challenge_prices inputs.length read bits)
  unfold storedActionHonestTapeJointCosted
  exact Nat.add_le_add_right (Nat.add_le_add ht (hj.trans_eq hp)) 3

end Zcash.Snark.ZeroKnowledge
