import Zcash.Snark.ZeroKnowledge.InteractiveReductionSource

/-!
# Interactive Action ZK with an operational PRNG resource class

The external assumption is PRNG security against the stated bounded program
family. Membership and the complete actual reduction's runtime are proved, not
assumed. The remaining loss is the protocol's statistical error plus the PRNG
test advantage. No concrete generator security or machine-code cost is asserted.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common
open scoped ENNReal

/-- The actual seeded interactive experiment has error `epsilon(m) + eta`, with resource admissibility discharged. -/
theorem costedUniformSeedActionZk_test_error_bound [Fintype VestaG]
    (prices : ActionReductionPrices) (inputs : List (PublicInputs Fp))
    (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
      (fun i : Fin inputs.length => inputs[i.val]) witness) (hW : W ≠ 0)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) (auxiliary : List (Fin challengeDigestCard))
    (program : RecordedTestProgram) (seedBits : ℕ)
    (generate : (Fin seedBits → Bool) → RawPrivateTape inputs.length) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits generate (PMF.pure ())
      (interactiveReductionAdmissible prices
        (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
        (interactivePrngTimeBound prices
          (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) program)) η) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let publicInputs := fun i : Fin inputs.length => inputs[i.val]
    let real := (actionZkProverFromSource urs rfl publicInputs witness (uniformSeedTapeSource seedBits generate)).map
      (interactiveViewTest program auxiliary)
    let simulated := (actionZkSimulator urs rfl publicInputs).map (interactiveViewTest program auxiliary)
    PMFEventBiasLE real simulated (plonkSimulationErrorBound inputs.length + η) ∧
      PMFEventBiasLE simulated real (plonkSimulationErrorBound inputs.length + η) := by
  have h := uniformSeedActionZk_test_error_bound
    ({ k := 11, g := generators, w := W, u := U } : URS VestaG) rfl
    (fun i : Fin inputs.length => inputs[i.val]) witness hvalid hW (PMF.pure ()) seedBits generate
    (fun _ view => PMF.pure (interactiveViewTest program auxiliary view))
    (interactiveReductionAdmissible prices
      (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary)
      (interactivePrngTimeBound prices
        (ActionReductionData.ofReference inputs generators W U witness vkTranscriptRepr cache auxiliary) program)) η secure
    (actionPrngReduction_mem_costed prices inputs generators W U witness vkTranscriptRepr cache auxiliary program)
  simpa only [PMF.pure_bind] using h

end Zcash.Snark.ZeroKnowledge
