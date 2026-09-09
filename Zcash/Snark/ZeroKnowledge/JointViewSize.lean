import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorCost

/-! # Exact storage dimensions of a fully materialized joint view -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Every typed joint view retains all commitment slots, five-field observations, and IPA rounds. -/
theorem materializePlonkJointView_shape {actions k : ℕ} {G : Type*}
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    let stored := materializePlonkJointView view
    stored.1.1.length = 22 * actions + 10 ∧
      stored.1.2.1.length = view.1.2.1.length ∧
      (∀ row ∈ stored.1.2.1, row.length = 5) ∧ stored.2.messages.length = k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [materializePlonkJointView, materializePlonkMaskView, List.length_ofFn]
  · simp only [materializePlonkJointView, materializePlonkMaskView, List.length_map]
  · intro row hrow
    simp only [materializePlonkJointView, materializePlonkMaskView, List.mem_map] at hrow
    obtain ⟨values, _, rfl⟩ := hrow
    exact List.length_ofFn
  · simp only [materializePlonkJointView, materializedIpaTranscript, List.length_ofFn]

end Zcash.Snark.ZeroKnowledge
