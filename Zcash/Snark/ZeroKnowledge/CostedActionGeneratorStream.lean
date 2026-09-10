import Zcash.Snark.ZeroKnowledge.CostedActionPrng
import Zcash.Snark.ZeroKnowledge.StreamTestProgram
import Zcash.Snark.ZeroKnowledge.ActionGeneratorStreamPrng

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open MeasureTheory
open scoped ENNReal

/-- Complete seeded-stream simulation with both actual PRNG reductions' resource conditions discharged.
The private generator continues across attempts; no generated-block independence or termination premise is added. -/
theorem costedGeneratedUnlimitedActionOracle_simulation_capstone [Fintype VestaG] {Generator : Type*}
    (prices : ActionReductionPrices) (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation ({ k := 11, g := generators, w := W, u := U } : URS VestaG)
      rfl (fun i : Fin inputs.length => inputs[i.val]) witness)
    (hpositive : 1 ≤ inputs.length) (hsize : inputs.length ≤ 65535) (hW : W ≠ 0)
    (vkTranscriptRepr : Fp) (next : Generator → Fin challengeDigestCard × Generator)
    (seedBits : ℕ) (initState : (Fin seedBits → Bool) → Generator) (budget : ℕ)
    (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard)) (program : StreamTestProgram) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits
      (fun seed => actionGeneratorRetryTape next inputs.length budget (initState seed)) (PMF.pure ())
      (actionReductionAdmissible prices
        (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) budget
        (recordedPrngViewAndTailTimeBound prices
          (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) program.toRecorded budget)) η) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let actual := (actionGeneratedOracleRetryStream urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr
      next seedBits initState cache).map (streamViewTest program auxiliary)
    let ideal := (actionOracleBitRetryStream urs rfl (fun i : Fin inputs.length => inputs[i.val]) vkTranscriptRepr cache).map
      (streamViewTest program auxiliary)
    let error := 2 * (oracleRetryPotential inputs.length cache.length + actionOracleRetryRate inputs.length ^ budget + η)
    MeasureEventBiasLE actual ideal error ∧ MeasureEventBiasLE ideal actual error := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let publicInputs := fun i : Fin inputs.length => inputs[i.val]
  let data := ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary
  let timeBound := recordedPrngViewAndTailTimeBound prices data program.toRecorded budget
  let admitted := actionReductionAdmissible prices data budget timeBound
  have hcompiled := actionOracleRecordPrngReduction_mem_costed prices inputs generators W U witness vkTranscriptRepr cache auxiliary
    program.toRecorded budget timeBound (Nat.le_max_left _ _)
  have heq := funext (streamViewTest_recorded program auxiliary)
  have hview : actionOracleRecordPrngReduction urs rfl publicInputs witness vkTranscriptRepr budget cache
      (fun output => streamViewTest program auxiliary (fun index => output.1.attempts[index]?)) ∈ admitted := by
    rewrite [heq]
    exact hcompiled
  have htail := actionOracleRecordPrngReduction_mem_costed prices inputs generators W U witness vkTranscriptRepr cache auxiliary
    recordedExhaustionTest budget timeBound (Nat.le_max_right _ _)
  exact generatedUnlimitedActionOracle_simulation_capstone urs rfl publicInputs witness hvalid hpositive hsize hW vkTranscriptRepr
    next seedBits initState budget cache (streamViewTest program auxiliary) (streamViewTest_measurable program auxiliary)
    admitted η secure hview htail

end Zcash.Snark.ZeroKnowledge
