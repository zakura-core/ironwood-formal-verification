import Zcash.Snark.ZeroKnowledge.Distribution

/-!
# Exceptional branches under an arbitrary private-state law

Private material contains lists of row vectors, so its ambient type need not be finite.
The PMF still assigns total mass one. Agreement outside an exceptional set therefore
gives the same simulation bound by that set's probability, without conditioning it away.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open scoped ENNReal

/-- Agreement off a private bad event bounds both directions of the mixed-law comparison. -/
theorem arbitraryMixedLaws_error_bound {C A : Type*}
    (coins : PMF C) (actual ideal : C → PMF A) (good : C → Prop) [DecidablePred good]
    (hgood : ∀ c, good c → actual c = ideal c) :
    PMFEventBiasLE (coins.bind actual) (coins.bind ideal)
        (coins.toOuterMeasure {c | ¬ good c}) ∧
      PMFEventBiasLE (coins.bind ideal) (coins.bind actual)
        (coins.toOuterMeasure {c | ¬ good c}) := by
  have hdirection (f g : C → PMF A) (hfg : ∀ c, good c → f c = g c) :
      PMFEventBiasLE (coins.bind f) (coins.bind g) (coins.toOuterMeasure {c | ¬ good c}) := by
    intro event
    have hpoint (c : C) : (f c).toOuterMeasure event ≤
        (g c).toOuterMeasure event + (if good c then 0 else 1) := by
      by_cases hc : good c
      · rw [if_pos hc, hfg c hc, add_zero]
      · rw [if_neg hc]
        exact eventBias_le_one (f c) (g c) event
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' c, coins c * ((g c).toOuterMeasure event + (if good c then 0 else 1)) :=
        ENNReal.tsum_le_tsum fun c => mul_le_mul_right (hpoint c) (coins c)
      _ = _ := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add]
        congr 1
        rw [PMF.toOuterMeasure_apply]
        apply tsum_congr
        intro c
        by_cases hc : good c <;> simp [hc]
  exact ⟨hdirection actual ideal hgood,
    hdirection ideal actual (fun c hc => (hgood c hc).symm)⟩

end Zcash.Snark.ZeroKnowledge
