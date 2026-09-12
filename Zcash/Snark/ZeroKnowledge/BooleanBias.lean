import Zcash.Common.Oracle.Model

/-!
# Boolean distinguishing advantage and event bias

For a normalized Boolean output, bounding the probability of `true` in both
directions bounds every output event. These statements concern the output of
one test, not statistical distance between that test's input distributions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open scoped ENNReal

/-- The reverse acceptance bound controls the complementary Boolean outcome. -/
theorem boolean_false_le {actual ideal : PMF Bool} {error : ℝ≥0∞}
    (h : ideal true ≤ actual true + error) : actual false ≤ ideal false + error := by
  have ha : actual false + actual true = 1 := by
    simpa only [tsum_bool] using actual.tsum_coe
  have hi : ideal false + ideal true = 1 := by
    simpa only [tsum_bool] using ideal.tsum_coe
  apply (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1
  calc
    actual false + 1 = ideal true + (actual false + ideal false) := by rw [← hi]; ring
    _ ≤ (actual true + error) + (actual false + ideal false) := add_le_add h le_rfl
    _ = (ideal false + error) + 1 := by rw [← ha]; ring

/-- Two acceptance-probability inequalities control every event of a Boolean output. -/
theorem boolean_event_bias {actual ideal : PMF Bool} {error : ℝ≥0∞}
    (forward : actual true ≤ ideal true + error)
    (reverse : ideal true ≤ actual true + error) : PMFEventBiasLE actual ideal error := by
  have hfalse := boolean_false_le reverse
  intro event
  by_cases ht : true ∈ event <;> by_cases hf : false ∈ event
  · have heq : event = Set.univ := by ext b; cases b <;> simp [ht, hf]
    rw [heq, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    simp only [Set.indicator_univ, actual.tsum_coe, ideal.tsum_coe]
    exact le_self_add
  · have heq : event = {true} := by ext b; cases b <;> simp [ht, hf]
    simpa only [heq, PMF.toOuterMeasure_apply_singleton] using forward
  · have heq : event = {false} := by ext b; cases b <;> simp [ht, hf]
    simpa only [heq, PMF.toOuterMeasure_apply_singleton] using hfalse
  · have heq : event = ∅ := by ext b; cases b <;> simp [ht, hf]
    simp [heq]

/-- Acceptance advantage and two-sided event bias are equivalent on Boolean outputs. -/
theorem boolean_event_bias_iff {actual ideal : PMF Bool} {error : ℝ≥0∞} :
    (PMFEventBiasLE actual ideal error ∧ PMFEventBiasLE ideal actual error) ↔
      (actual true ≤ ideal true + error ∧ ideal true ≤ actual true + error) := by
  constructor
  · intro h
    exact ⟨by simpa only [PMF.toOuterMeasure_apply_singleton] using h.1 {true},
      by simpa only [PMF.toOuterMeasure_apply_singleton] using h.2 {true}⟩
  · intro h
    exact ⟨boolean_event_bias h.1 h.2, boolean_event_bias h.2 h.1⟩

end Zcash.Snark.ZeroKnowledge
