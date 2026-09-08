import Zcash.Snark.ZeroKnowledge.MeasureEventBias

/-!
# Lifting a uniform finite-prefix bound to complete streams

Every cylinder depends on a bounded prefix, even if its coordinates are not
consecutive. Approximation in the sum of the two finite measures then extends
the same bound to all measurable stream events, with no extra loss.
-/

namespace Zcash.Snark.ZeroKnowledge

open MeasureTheory
open scoped ENNReal

/-- A uniform bound for all finite prefixes applies to every measurable event of the full stream. -/
theorem measureEventBias_of_prefixes {A : Type*} [MeasurableSpace A]
    (actual ideal : Measure (ℕ → A)) [IsFiniteMeasure actual] [IsFiniteMeasure ideal]
    (error : ℝ≥0∞)
    (h : ∀ budget, MeasureEventBiasLE
      (actual.map (fun stream (i : Fin budget) => stream i.val))
      (ideal.map (fun stream (i : Fin budget) => stream i.val)) error) :
    MeasureEventBiasLE actual ideal error := by
  apply measureEventBias_of_cylinders actual ideal error
  intro event he
  obtain ⟨indices, selected, hselected, rfl⟩ := (mem_measurableCylinders event).mp he
  let budget := indices.sup id + 1
  let select : (Fin budget → A) → (i : indices) → A := fun tapePrefix i =>
    tapePrefix ⟨i.val, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  have hm : Measurable select := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hs := hselected.preimage hm
  have hp := h budget (select ⁻¹' selected) hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.map_apply (by fun_prop) hs] at hp
  exact hp

end Zcash.Snark.ZeroKnowledge
