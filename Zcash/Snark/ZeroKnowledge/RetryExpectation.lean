import Zcash.Snark.ZeroKnowledge.RetryProjection

/-!
# Expected attempts in the unlimited retry experiment

The exact length tail yields both the expected number of attempts and a finite
upper bound whenever the one-attempt retry probability is strictly below one.
-/

namespace Zcash.Snark.ZeroKnowledge

open scoped ENNReal

/-- A natural-valued discrete expectation is the sum of its strict tail probabilities. -/
theorem natExpectation_eq_tsum_tail {A : Type*} (law : PMF A) (count : A → ℕ) :
    (∑' value, law value * (count value : ℝ≥0∞)) =
      ∑' budget : ℕ, law.toOuterMeasure {value | budget < count value} := by
  classical
  have hcount (value : A) : (count value : ℝ≥0∞) =
      ∑' budget : ℕ, if budget < count value then (1 : ℝ≥0∞) else 0 := by
    rw [tsum_eq_sum (s := Finset.range (count value)) (fun budget h => by
      simp only [Finset.mem_range, not_lt] at h
      simp [Nat.not_lt_of_ge h])]
    symm
    calc
      _ = ∑ _ ∈ Finset.range (count value), (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro budget hb
        exact if_pos (Finset.mem_range.mp hb)
      _ = _ := by simp
  simp_rw [hcount, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro budget
  rw [law.toOuterMeasure_apply]
  apply tsum_congr
  intro value
  by_cases h : budget < count value <;> simp [Set.indicator, h]

/-- The complete independent retry policy uses exactly the geometric mean number of attempts. -/
theorem unlimitedRetainedRetries_expected_attempts {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] (hrate : law.toOuterMeasure retry < 1) :
    (∑' history, (unlimitedRetainedRetries law retry hrate) history *
      (history.attempts.length : ℝ≥0∞)) = (1 - law.toOuterMeasure retry)⁻¹ := by
  rw [natExpectation_eq_tsum_tail]
  simp only [unlimitedRetainedRetries_length_tail, ENNReal.tsum_geometric]

/-- A one-attempt retry bound gives the stated upper bound on expected attempts. -/
theorem unlimitedRetainedRetries_expected_attempts_le {A : Type*} (law : PMF A) (retry : Set A)
    [DecidablePred (fun a => a ∈ retry)] {failure : ℝ≥0∞}
    (hfailure : law.toOuterMeasure retry ≤ failure) (hrate : failure < 1) :
    (∑' history, (unlimitedRetainedRetries law retry (hfailure.trans_lt hrate)) history *
      (history.attempts.length : ℝ≥0∞)) ≤ (1 - failure)⁻¹ := by
  rw [unlimitedRetainedRetries_expected_attempts]
  exact ENNReal.inv_le_inv.mpr (tsub_le_tsub_left hfailure 1)

end Zcash.Snark.ZeroKnowledge
