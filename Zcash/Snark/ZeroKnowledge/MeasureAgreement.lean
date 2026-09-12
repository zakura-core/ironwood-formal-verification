import Zcash.Snark.ZeroKnowledge.MeasureEventBias

/-!
# Measurable observations agreeing outside a bad event

The event may contain every nonterminating execution. No normalization or
discarding of failed observations is performed.
-/

namespace Zcash.Snark.ZeroKnowledge

open MeasureTheory
open scoped ENNReal

/-- A common underlying probability space bounds disagreement by the full bad-event mass. -/
theorem measureEventBias_map_of_agree {Source Output : Type*}
    [MeasurableSpace Source] [MeasurableSpace Output] (law : Measure Source)
    (actual ideal : Source → Output) (ha : Measurable actual) (hi : Measurable ideal)
    (bad : Set Source) (h : ∀ value ∉ bad, actual value = ideal value) :
    MeasureEventBiasLE (law.map actual) (law.map ideal) (law bad) := by
  intro event he
  rw [Measure.map_apply ha he, Measure.map_apply hi he]
  apply (measure_mono (show actual ⁻¹' event ⊆ (ideal ⁻¹' event) ∪ bad from ?_)).trans
    (measure_union_le _ _)
  intro value hv
  by_cases hb : value ∈ bad
  · exact Or.inr hb
  · exact Or.inl (by simpa only [Set.mem_preimage, h value hb] using hv)

end Zcash.Snark.ZeroKnowledge
