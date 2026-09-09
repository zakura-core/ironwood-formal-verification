import Zcash.Snark.ZeroKnowledge.StoredActionHistoryTrace

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The full transcript recomputation budget depends only on stored dimensions and fixed primitive prices. -/
def storedActionHistoryTraceCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions privateLength historyLength : ℕ)
    (key : StoredPlonkKey) : ℕ :=
  22 * (2 * historyLength + read + 4) + 485 + 11 * (read + 55) + 26 +
    storedActionHonestFieldTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions privateLength (read + 55) key (storedPlonkChallengePriceModel 11 read) + 2

/-- Preparing the history and running the complete real prover discharges every transcript producer cost. -/
theorem storedActionHistoryTraceCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (privateFields : List Fp) (history : List (Fin challengeDigestCard)) :
    (storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) privateFields history).2 ≤
      storedActionHistoryTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length privateFields.length history.length (StoredPlonkKey.encode vk) := by
  let ch := storedHistoryChallengesCosted read history
  have hc := storedHistoryChallengesCosted_cost_le read history
  have ht := storedActionHonestFieldTraceCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness ch.1 (read + 55) privateFields
    (storedHistoryChallengesCosted_readBound read history)
  have hp := storedActionHonestFieldTraceCostBudget_congr_prices costs node equal read omegaAccess canonicalRead compare
    groupAdd groupScale inputs.length privateFields.length (read + 55) (StoredPlonkKey.encode vk)
    ch.1 (storedPlonkChallengePriceModel 11 read) (storedHistoryChallengesCosted_prices read history)
  unfold storedActionHistoryTraceCosted
  exact Nat.add_le_add_right (Nat.add_le_add hc (ht.trans_eq hp)) 2

/-- A public bound on the received-history length gives one common recomputation budget. -/
theorem storedActionHistoryTraceCostBudget_mono_history (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions privateLength left right : ℕ)
    (key : StoredPlonkKey) (h : left ≤ right) :
    storedActionHistoryTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions privateLength left key ≤
    storedActionHistoryTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions privateLength right key := by
  unfold storedActionHistoryTraceCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
