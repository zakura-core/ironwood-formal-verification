import Zcash.Snark.ZeroKnowledge.PlonkSuccessBounds

/-!
# A binary bound for the reference simulation error

The exact budget is affine in the Action count. For every positive count it is
at most that count times the one-Action budget. Combining the proved wide-reduction
bound with kernel-checked integer arithmetic gives the readable bound
epsilon(m) < m * 2^(-238). This concerns the unconditioned reference experiment.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- The constant part of the affine budget is charged at most once per Action. -/
theorem plonkSimulationErrorBound_le_actions_mul_one {actions : ℕ} (hsize : 1 ≤ actions) :
    plonkSimulationErrorBound actions ≤ actions * plonkSimulationErrorBound 1 := by
  change (((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
      ((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias ≤
    actions * ((46995 : ℝ≥0∞) / scalarFieldOrder + 218 * challenge255Bias)
  calc
    _ ≤ (((actions * 46995 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        ((actions * 218 : ℕ) : ℝ≥0∞) * challenge255Bias := by
      apply add_le_add
      · apply ENNReal.div_le_div_right
        exact_mod_cast (show 42882 * actions + 4113 ≤ actions * 46995 by omega)
      · exact mul_le_mul_left
          (by exact_mod_cast (show 148 * actions + 70 ≤ actions * 218 by omega)) _
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      ring

set_option exponentiation.threshold 1024 in
/-- The one-Action budget is strictly below 2^(-238), using the proved per-sample bias bound. -/
theorem plonkSimulationErrorBound_one_lt_two_pow :
    plonkSimulationErrorBound 1 < 1 / (2 : ℝ≥0∞) ^ 238 := by
  change (46995 : ℝ≥0∞) / scalarFieldOrder + 218 * challenge255Bias < _
  calc
    _ ≤ (46995 : ℝ≥0∞) / scalarFieldOrder + 218 * (1 / 2 ^ 260) :=
      add_le_add le_rfl (mul_le_mul_right fieldSample_bias_le 218)
    _ < 1 / 2 ^ 238 := by
      have hp0 : (scalarFieldOrder : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
      have hpt : (scalarFieldOrder : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
      have hb0 : (2 : ℝ≥0∞) ^ 260 ≠ 0 := pow_ne_zero _ (by simp)
      have hbt : (2 : ℝ≥0∞) ^ 260 ≠ ∞ := ENNReal.pow_ne_top (by simp)
      have ht0 : (2 : ℝ≥0∞) ^ 238 ≠ 0 := pow_ne_zero _ (by simp)
      have htt : (2 : ℝ≥0∞) ^ 238 ≠ ∞ := ENNReal.pow_ne_top (by simp)
      have hnum : ((46995 : ℝ≥0∞) * 2 ^ 260 + 218 * scalarFieldOrder) * 2 ^ 238 <
          scalarFieldOrder * 2 ^ 260 := by
        exact_mod_cast (show (46995 * 2 ^ 260 + 218 * scalarFieldOrder) * 2 ^ 238 <
          scalarFieldOrder * 2 ^ 260 by decide)
      apply (ENNReal.mul_lt_mul_iff_left ht0 htt).1
      apply (ENNReal.mul_lt_mul_iff_left hp0 hpt).1
      apply (ENNReal.mul_lt_mul_iff_left hb0 hbt).1
      calc
        _ = ((46995 / (scalarFieldOrder : ℝ≥0∞) * scalarFieldOrder) * 2 ^ 260 +
            218 * scalarFieldOrder * ((1 / 2 ^ 260) * 2 ^ 260)) * 2 ^ 238 := by ring
        _ = (46995 * 2 ^ 260 + 218 * scalarFieldOrder) * 2 ^ 238 := by
          rw [ENNReal.div_mul_cancel hp0 hpt, ENNReal.div_mul_cancel hb0 hbt, mul_one]
        _ < scalarFieldOrder * 2 ^ 260 := hnum
        _ = _ := by rw [ENNReal.div_mul_cancel ht0 htt, one_mul]

/-- For every positive Action count, the reference simulation error is below m * 2^(-238). -/
theorem plonkSimulationErrorBound_lt_actions_mul_two_pow {actions : ℕ} (hsize : 1 ≤ actions) :
    plonkSimulationErrorBound actions < actions * (1 / (2 : ℝ≥0∞) ^ 238) := by
  have ha0 : (actions : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hat : (actions : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  exact (plonkSimulationErrorBound_le_actions_mul_one hsize).trans_lt
    ((ENNReal.mul_lt_mul_iff_right ha0 hat).2 plonkSimulationErrorBound_one_lt_two_pow)

end Zcash.Snark.ZeroKnowledge
