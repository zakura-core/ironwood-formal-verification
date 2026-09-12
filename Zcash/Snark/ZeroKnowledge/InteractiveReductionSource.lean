import Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram
import Zcash.Snark.ZeroKnowledge.ActionPrngSecurity

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

/-- The complete budget of the actual interactive PRNG reduction for a given concrete view circuit. -/
def interactivePrngTimeBound (prices : ActionReductionPrices) (data : ActionReductionData)
    (program : RecordedTestProgram) : ℕ :=
  (InteractiveReductionProgram.observed program).costBudget prices data (22 * 512) (fieldSampleCount data.inputs.length)

/-- The operational program has exactly the old interactive PRNG reduction law for every candidate tape. -/
theorem InteractiveReductionProgram.kernel_observed (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard)) (program : RecordedTestProgram) :
    (.observed program : InteractiveReductionProgram).kernel prices
      (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) =
      (fun _ => actionPrngReduction ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
        (fun i : Fin inputs.length => inputs[i.val]) witness (fun view => PMF.pure (interactiveViewTest program auxiliary view))) := by
  funext token privateTape
  unfold kernel
  dsimp only [evalCosted]
  have hresult := funext (fun bits => interactiveTestCosted_result prices inputs generators W U witness
    vkTranscriptRepr cache auxiliary program bits privateTape)
  let finish := fun ch : Challenges 11 Fp => interactiveViewTest program auxiliary (actionZkRunFromRawTape
    ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
    (fun i : Fin inputs.length => inputs[i.val]) witness ch privateTape)
  have h := congrArg (PMF.map finish) (uniformBitPlonkChallenges 11)
  simp only [PMF.map_comp, Function.comp_def] at h
  exact (congrArg (fun run => (PMF.uniformOfFintype (Fin (22 * 512) → Bool)).map run) hresult).trans h

/-- Membership of the actual real-prover-and-test reduction follows without an assumed cost or class certificate. -/
theorem actionPrngReduction_mem_costed (prices : ActionReductionPrices)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard)) (program : RecordedTestProgram) :
    let data := ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary
    (fun _ => actionPrngReduction ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
      (fun i : Fin inputs.length => inputs[i.val]) witness (fun view => PMF.pure (interactiveViewTest program auxiliary view))) ∈
      interactiveReductionAdmissible prices data (interactivePrngTimeBound prices data program) :=
  ⟨ActionReductionData.ofReference_wellFormed inputs generators W U witness vkTranscriptRepr cache auxiliary,
    .observed program, le_rfl,
    (InteractiveReductionProgram.kernel_observed prices inputs generators W U witness vkTranscriptRepr cache auxiliary program).symm⟩

end Zcash.Snark.ZeroKnowledge
