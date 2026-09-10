import Zcash.Snark.ZeroKnowledge.ActionReductionProgram
import Zcash.Snark.ZeroKnowledge.ActionOracleRecordedPrng

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey

/-- Complete executable budget for the reference reduction and one concrete recorded-view test. -/
def recordedPrngTimeBound (prices : ActionReductionPrices) (data : ActionReductionData)
    (program : RecordedTestProgram) (budget : ℕ) : ℕ :=
  (ActionReductionProgram.observed program).costBudget prices data budget ((budget * 22) * 512)

/-- One security class large enough for both the view test and the generated-exhaustion test. -/
def recordedPrngViewAndTailTimeBound (prices : ActionReductionPrices) (data : ActionReductionData)
    (program : RecordedTestProgram) (budget : ℕ) : ℕ :=
  max (recordedPrngTimeBound prices data program budget) (recordedPrngTimeBound prices data recordedExhaustionTest budget)

/-- The executable observed program is exactly the original complete recorded-view PRNG reduction. -/
theorem ActionReductionProgram.kernel_observed (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (program : RecordedTestProgram) (budget : ℕ) :
    (ActionReductionProgram.observed program).kernel prices
        (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) budget =
      actionOracleRecordPrngReduction ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
        rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr budget cache (recordedViewTest program auxiliary) := by
  funext token privateTape
  unfold kernel
  dsimp only [ActionReductionProgram.evalCosted]
  have hresult := funext (fun bits : Fin ((budget * 22) * 512) → Bool =>
    observedReductionCosted_result prices inputs generators W U witness vkTranscriptRepr cache auxiliary program budget bits privateTape)
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  have h := congrArg (PMF.map (fun replies : OracleReplyRetryTape 11 budget =>
    recordedViewTest program auxiliary (actionOracleRecordFromRawTapes urs rfl (fun i : Fin inputs.length => inputs[i.val])
      witness vkTranscriptRepr replies privateTape cache))) (uniformRawMatrixBits budget 22)
  simp only [PMF.map_comp, Function.comp_def] at h
  exact (congrArg (fun run => (PMF.uniformOfFintype (Fin ((budget * 22) * 512) → Bool)).map run) hresult).trans h

/-- The proved complete runtime supplies the original reduction's membership at any larger explicit limit. -/
theorem actionOracleRecordPrngReduction_mem_costed (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (program : RecordedTestProgram) (budget timeBound : ℕ)
    (hbound : (ActionReductionProgram.observed program).costBudget prices
      (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
      budget ((budget * 22) * 512) ≤ timeBound) :
    actionOracleRecordPrngReduction ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
        rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr budget cache (recordedViewTest program auxiliary) ∈
      actionReductionAdmissible prices (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
        budget timeBound := by
  refine ⟨ActionReductionData.ofReference_wellFormed inputs generators W U witness vkTranscriptRepr cache auxiliary,
    .observed program, hbound, ?_⟩
  exact (ActionReductionProgram.kernel_observed prices inputs generators W U witness vkTranscriptRepr cache auxiliary program budget).symm

/-- At the derived complete budget no resource-class premise remains to be supplied by the caller. -/
theorem actionOracleRecordPrngReduction_mem_ownBudget (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (program : RecordedTestProgram) (budget : ℕ) :
    let data := ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary
    actionOracleRecordPrngReduction ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
        rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr budget cache (recordedViewTest program auxiliary) ∈
      actionReductionAdmissible prices data budget ((ActionReductionProgram.observed program).costBudget prices data budget ((budget * 22) * 512)) :=
  actionOracleRecordPrngReduction_mem_costed prices inputs generators W U witness vkTranscriptRepr cache auxiliary program budget _ le_rfl

end Zcash.Snark.ZeroKnowledge
