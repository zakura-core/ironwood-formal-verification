import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamTail

/-!
# Nontermination stays visible in the complete observation

A clipped history always has an absent suffix. Comparing a complete history
with that exact clipping therefore bounds nontermination by its truncation loss.
-/

namespace Zcash.Snark.ZeroKnowledge

open MeasureTheory
open scoped ENNReal

/-- Clipping at any finite budget produces no nonterminating stream. -/
theorem truncateRetryStream_nontermination_measure_zero {Value : Type*}
    [MeasurableSpace (Option Value)] [MeasurableSingletonClass (Option Value)]
    (law : Measure (ℕ → Option Value)) (budget : ℕ) :
    (law.map (truncateRetryStream budget)) retryStreamNontermination = 0 := by
  rw [Measure.map_apply (truncateRetryStream_measurable budget) retryStreamNontermination_measurable]
  have he : (truncateRetryStream budget) ⁻¹' retryStreamNontermination = (∅ : Set (ℕ → Option Value)) := by
    ext stream
    simp only [Set.mem_preimage, retryStreamNontermination, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact h budget (by simp only [truncateRetryStream, Nat.lt_irrefl, if_false])
  rw [he, measure_empty]

end Zcash.Snark.ZeroKnowledge
