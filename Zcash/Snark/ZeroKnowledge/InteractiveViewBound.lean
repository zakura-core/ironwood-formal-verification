import Zcash.Snark.ZeroKnowledge.InteractiveViewCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey

/-- Full real proof, canonical observation, second challenge materialization, and frame construction. -/
def interactiveHistoryViewCostBudget (prices : ActionReductionPrices) (data : ActionReductionData)
    (privateLength historyLength : ℕ) : ℕ :=
  storedActionHistoryTraceCostBudget prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs.length privateLength historyLength data.key +
    (22 * (prices.read + 57) + 136 +
      (72 * data.inputs.length + 107) * (prices.read + 55 + 44 + 2 * prices.read + 3 * prices.equal + 3600) + 3) +
    (22 * (prices.read + 57) + 136) + 14

/-- Stored source inputs discharge the complete interactive computation bound, even on exceptional tapes. -/
theorem interactiveHistoryViewCosted_cost_le (prices : ActionReductionPrices) (data : ActionReductionData)
    (hdata : data.WellFormed) (privateFields : List Fp) (history : List (Fin challengeDigestCard)) :
    (interactiveHistoryViewCosted prices data privateFields history).2 ≤
      interactiveHistoryViewCostBudget prices data privateFields.length history.length := by
  let produced := storedActionHistoryTraceCosted prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs data.setup data.key data.witnessRows
    privateFields history
  have hp : produced.2 ≤ storedActionHistoryTraceCostBudget prices.field prices.node prices.equal prices.read prices.omegaAccess
      prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs.length privateFields.length history.length data.key := by
    obtain ⟨generators, W, U, witness, hs, hk, hw⟩ := hdata
    unfold produced
    rewrite [hs, hk, hw]
    exact storedActionHistoryTraceCosted_cost_le prices.field prices.node prices.equal prices.read prices.omegaAccess
      prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
      (actionReferenceKey (actions := data.inputs.length) ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
        rfl actionCircuit_newFixedCols_eq_fifteen) witness privateFields history
  have hread := storedActionHistoryTraceCosted_readBound prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs data.setup data.key data.witnessRows privateFields history
  have hlength := storedActionHistoryTraceCosted_length_le prices.field prices.node prices.equal prices.read prices.omegaAccess
    prices.canonicalRead prices.compare prices.groupAdd prices.groupScale data.inputs data.setup data.key data.witnessRows privateFields history
  have ho := canonicalProtocolObserverCosted_cost_le prices.equal prices.read produced.1.1 produced.1.2 (prices.read + 55) hread
  have hs := plonkChallengeSequenceCosted_cost_le produced.1.1 (prices.read + 55) hread
  have hobs := ho.trans (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_right (prices.read + 55 + 4 * 11 + 2 * prices.read + 3 * prices.equal + 3600) hlength) _) 3)
  unfold interactiveHistoryViewCosted interactiveHistoryViewCostBudget
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp hobs) hs) 14

end Zcash.Snark.ZeroKnowledge
