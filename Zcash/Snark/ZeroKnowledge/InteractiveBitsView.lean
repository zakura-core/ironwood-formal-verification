import Zcash.Snark.ZeroKnowledge.InteractiveViewBound
import Zcash.Snark.ZeroKnowledge.InteractiveChallengeBits

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

/-- The full interactive real prover consumes stored private words and independent stored verifier bits. -/
@[irreducible] def interactiveBitsViewCosted (prices : ActionReductionPrices) (data : ActionReductionData)
    (bits : List Bool) (privateWords : List (Fin challengeDigestCard)) : ActionRetryRecordedView × ℕ :=
  let fields := storedRawFieldsCosted (fieldSampleCount data.inputs.length) prices.read privateWords
  let replies := storedRawTapeCosted 22 prices.read bits
  let produced := interactiveHistoryViewCosted prices data fields.1 replies.1
  (produced.1, fields.2 + replies.2 + produced.2 + 3)

/-- Every private read, wide reduction, verifier bit, full proof, and observation is charged. -/
def interactiveBitsViewCostBudget (prices : ActionReductionPrices) (data : ActionReductionData)
    (bitLength privateLength : ℕ) : ℕ :=
  fieldSampleCount data.inputs.length * (2 * privateLength + prices.read + 4) +
    fieldSampleCount data.inputs.length * fieldSampleCount data.inputs.length + 1 +
    (22 * (512 * (2 * bitLength + prices.read + 4) + 264195) + 22 * 22 + 1) +
    interactiveHistoryViewCostBudget prices data (fieldSampleCount data.inputs.length) 22 + 3

/-- The interactive runtime bound has only stored-input shape conditions. -/
theorem interactiveBitsViewCosted_cost_le (prices : ActionReductionPrices) (data : ActionReductionData)
    (hdata : data.WellFormed) (bits : List Bool) (privateWords : List (Fin challengeDigestCard)) :
    (interactiveBitsViewCosted prices data bits privateWords).2 ≤
      interactiveBitsViewCostBudget prices data bits.length privateWords.length := by
  have hf := storedRawFieldsCosted_cost_le (fieldSampleCount data.inputs.length) prices.read privateWords
  have hr := storedRawTapeCosted_cost_le 22 prices.read bits
  have hp := interactiveHistoryViewCosted_cost_le prices data hdata
    (storedRawFieldsCosted (fieldSampleCount data.inputs.length) prices.read privateWords).1
    (storedRawTapeCosted 22 prices.read bits).1
  rewrite [storedRawFieldsCosted_length] at hp
  have hrl : (storedRawTapeCosted 22 prices.read bits).1.length = 22 := ofFnCosted_length _
  rewrite [hrl] at hp
  unfold interactiveBitsViewCosted interactiveBitsViewCostBudget
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hf hr) hp) 3

/-- The counted implementation returns the complete original interactive view on the same candidate private tape. -/
theorem interactiveBitsViewCosted_result (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (bits : Fin (22 * 512) → Bool) (privateTape : RawPrivateTape inputs.length) :
    (interactiveBitsViewCosted prices
      (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
      (List.ofFn bits) (List.ofFn privateTape)).1 =
      interactiveRecordedView (actionZkRunFromRawTape
        ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
        (fun i : Fin inputs.length => inputs[i.val]) witness
        (plonkChallengesFromTape (reduceFieldTape (rawBitsTapeEquiv 22 bits))) privateTape) := by
  unfold interactiveBitsViewCosted
  change (interactiveHistoryViewCosted prices
    (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
    (storedRawFieldsCosted (fieldSampleCount inputs.length) prices.read (List.ofFn privateTape)).1
    (storedRawTapeCosted 22 prices.read (List.ofFn bits)).1).1 = _
  rewrite [storedRawFieldsCosted_ofFn_result, storedRawTapeCosted_encode_result,
    interactiveHistoryViewCosted_result, plonkHistoryChallenges_ofFn]
  rfl

end Zcash.Snark.ZeroKnowledge
