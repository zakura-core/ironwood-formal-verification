import Zcash.Snark.ZeroKnowledge.PlonkSuccessBounds

/-!
# An explicit completeness error budget

The conservative union bound adds the honest emission-failure budget, the
real-to-simulator statistical distance, and the simulator's exceptional-challenge
budget. It counts aborted attempts and completed but rejected proofs together.
No attempt is conditioned on success.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- The additional exceptional-challenge budget used to establish simulator acceptance. -/
noncomputable def plonkVerifierRejectionBound : ℝ≥0∞ :=
  4113 / scalarFieldOrder + 22 * challenge255Bias

/-- An upper bound on abort or verifier rejection for one eleven-round reference attempt. -/
noncomputable def plonkCompletenessErrorBound (actions : ℕ) : ℝ≥0∞ :=
  plonkAttemptFailureBound actions + plonkSimulationErrorBound actions +
    plonkVerifierRejectionBound

/-- The explicit affine completeness budget, including both wide-reduction contributions. -/
theorem plonkCompletenessErrorBound_eq (actions : ℕ) :
    plonkCompletenessErrorBound actions =
      (((42904 * actions + 8271 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        ((296 * actions + 160 : ℕ) : ℝ≥0∞) * challenge255Bias := by
  simp only [plonkCompletenessErrorBound, plonkAttemptFailureBound,
    plonkSimulationErrorBound, plonkVerifierRejectionBound,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
  ring

/-- For a nonempty bundle, the constant terms cost at most the one-Action amount per Action. -/
theorem plonkCompletenessErrorBound_le_actions_mul_one {actions : ℕ} (hsize : 1 ≤ actions) :
    plonkCompletenessErrorBound actions ≤ actions * plonkCompletenessErrorBound 1 := by
  rw [plonkCompletenessErrorBound_eq, plonkCompletenessErrorBound_eq]
  change (((42904 * actions + 8271 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
      ((296 * actions + 160 : ℕ) : ℝ≥0∞) * challenge255Bias ≤
    actions * ((51175 : ℝ≥0∞) / scalarFieldOrder + 456 * challenge255Bias)
  calc
    _ ≤ (((actions * 51175 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        ((actions * 456 : ℕ) : ℝ≥0∞) * challenge255Bias := by
      apply add_le_add
      · apply ENNReal.div_le_div_right
        exact_mod_cast (show 42904 * actions + 8271 ≤ actions * 51175 by omega)
      · exact mul_le_mul_left
          (by exact_mod_cast (show 296 * actions + 160 ≤ actions * 456 by omega)) _
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      ring

set_option exponentiation.threshold 1024 in
/-- Kernel-checked arithmetic bounds the one-Action completeness error by `2^(-238)`. -/
theorem plonkCompletenessErrorBound_one_lt_two_pow :
    plonkCompletenessErrorBound 1 < 1 / (2 : ℝ≥0∞) ^ 238 := by
  rw [plonkCompletenessErrorBound_eq]
  change (51175 : ℝ≥0∞) / scalarFieldOrder + 456 * challenge255Bias < _
  calc
    _ ≤ (51175 : ℝ≥0∞) / scalarFieldOrder + 456 * (1 / 2 ^ 260) :=
      add_le_add le_rfl (mul_le_mul_right fieldSample_bias_le 456)
    _ < 1 / 2 ^ 238 := by
      have hp0 : (scalarFieldOrder : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
      have hpt : (scalarFieldOrder : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
      have hb0 : (2 : ℝ≥0∞) ^ 260 ≠ 0 := pow_ne_zero _ (by simp)
      have hbt : (2 : ℝ≥0∞) ^ 260 ≠ ∞ := ENNReal.pow_ne_top (by simp)
      have ht0 : (2 : ℝ≥0∞) ^ 238 ≠ 0 := pow_ne_zero _ (by simp)
      have htt : (2 : ℝ≥0∞) ^ 238 ≠ ∞ := ENNReal.pow_ne_top (by simp)
      have hnum : ((51175 : ℝ≥0∞) * 2 ^ 260 + 456 * scalarFieldOrder) * 2 ^ 238 <
          scalarFieldOrder * 2 ^ 260 := by
        exact_mod_cast (show (51175 * 2 ^ 260 + 456 * scalarFieldOrder) * 2 ^ 238 <
          scalarFieldOrder * 2 ^ 260 by decide)
      apply (ENNReal.mul_lt_mul_iff_left ht0 htt).1
      apply (ENNReal.mul_lt_mul_iff_left hp0 hpt).1
      apply (ENNReal.mul_lt_mul_iff_left hb0 hbt).1
      calc
        _ = ((51175 / (scalarFieldOrder : ℝ≥0∞) * scalarFieldOrder) * 2 ^ 260 +
            456 * scalarFieldOrder * ((1 / 2 ^ 260) * 2 ^ 260)) * 2 ^ 238 := by ring
        _ = (51175 * 2 ^ 260 + 456 * scalarFieldOrder) * 2 ^ 238 := by
          rw [ENNReal.div_mul_cancel hp0 hpt, ENNReal.div_mul_cancel hb0 hbt, mul_one]
        _ < scalarFieldOrder * 2 ^ 260 := hnum
        _ = _ := by rw [ENNReal.div_mul_cancel ht0 htt, one_mul]

/-- The complete one-attempt error is below `m * 2^(-238)` for every positive Action count. -/
theorem plonkCompletenessErrorBound_lt_actions_mul_two_pow {actions : ℕ} (hsize : 1 ≤ actions) :
    plonkCompletenessErrorBound actions < actions * (1 / (2 : ℝ≥0∞) ^ 238) := by
  have ha0 : (actions : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hat : (actions : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  exact (plonkCompletenessErrorBound_le_actions_mul_one hsize).trans_lt
    ((ENNReal.mul_lt_mul_iff_right ha0 hat).2 plonkCompletenessErrorBound_one_lt_two_pow)

end Zcash.Snark.ZeroKnowledge
