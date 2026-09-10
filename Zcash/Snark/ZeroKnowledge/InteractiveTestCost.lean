import Zcash.Snark.ZeroKnowledge.InteractiveBitsView
import Zcash.Snark.ZeroKnowledge.RecordedTestProgram

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

/-- A concrete Boolean circuit tests the original full interactive verifier view and stored auxiliary words. -/
def interactiveViewTest (program : RecordedTestProgram) (auxiliary : List (Fin challengeDigestCard))
    (view : Challenges 11 Fp × ProverAttemptResult) : Bool :=
  recordedViewTest program auxiliary (interactiveRecordedView view)

/-- Run the complete actual interactive prover, copy auxiliary data, and execute every test instruction. -/
@[irreducible] def interactiveTestCosted (prices : ActionReductionPrices) (data : ActionReductionData)
    (program : RecordedTestProgram) (bits : List Bool) (privateWords : List (Fin challengeDigestCard)) : Bool × ℕ :=
  let auxiliary := copyAuxiliaryWordsCosted prices.read data.auxiliary
  let produced := interactiveBitsViewCosted prices data bits privateWords
  let tested := recordedViewTestCosted program prices.read prices.canonicalRead auxiliary.1 produced.1
  (tested.1, auxiliary.2 + produced.2 + tested.2 + 3)

/-- The real-prover-and-test budget includes the full supplied auxiliary input. -/
def interactiveTestCostBudget (prices : ActionReductionPrices) (data : ActionReductionData)
    (program : RecordedTestProgram) (bitLength privateLength : ℕ) : ℕ :=
  data.auxiliary.length * (prices.read + 2) + 1 +
    interactiveBitsViewCostBudget prices data bitLength privateLength +
    recordedViewTestCostBudget program prices.read prices.canonicalRead + 3

/-- All execution-cost conditions are discharged for this actual complete interactive reduction. -/
theorem interactiveTestCosted_cost_le (prices : ActionReductionPrices) (data : ActionReductionData)
    (hdata : data.WellFormed) (program : RecordedTestProgram) (bits : List Bool)
    (privateWords : List (Fin challengeDigestCard)) :
    (interactiveTestCosted prices data program bits privateWords).2 ≤
      interactiveTestCostBudget prices data program bits.length privateWords.length := by
  have ha := copyAuxiliaryWordsCosted_cost_le prices.read data.auxiliary
  have hp := interactiveBitsViewCosted_cost_le prices data hdata bits privateWords
  have ht := recordedViewTestCosted_cost_le program prices.read prices.canonicalRead
    (copyAuxiliaryWordsCosted prices.read data.auxiliary).1 (interactiveBitsViewCosted prices data bits privateWords).1
  unfold interactiveTestCosted interactiveTestCostBudget
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ha hp) ht) 3

/-- The counted circuit tests exactly the original view on the candidate private tape. -/
theorem interactiveTestCosted_result (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (program : RecordedTestProgram) (bits : Fin (22 * 512) → Bool) (privateTape : RawPrivateTape inputs.length) :
    (interactiveTestCosted prices (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
      program (List.ofFn bits) (List.ofFn privateTape)).1 =
      interactiveViewTest program auxiliary (actionZkRunFromRawTape
        ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
        (fun i : Fin inputs.length => inputs[i.val]) witness
        (plonkChallengesFromTape (reduceFieldTape (rawBitsTapeEquiv 22 bits))) privateTape) := by
  unfold interactiveTestCosted
  dsimp only
  rewrite [recordedViewTestCosted_result, copyAuxiliaryWordsCosted_result, interactiveBitsViewCosted_result]
  rfl

end Zcash.Snark.ZeroKnowledge
