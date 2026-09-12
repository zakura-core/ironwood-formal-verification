import Zcash.Snark.ZeroKnowledge.PlonkFailures

/-!
# Numerical budgets for successful full-prover views

The raw comparison and honest failure bounds have different meanings. Their sum
bounds failure on both sides, giving a common lower bound on success probability.
The finite range below is an arithmetic certificate, with no protocol limit inferred.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- The joint reference simulation budget, before conditioning on success. -/
noncomputable def plonkSimulationErrorBound (actions : ℕ) : ℝ≥0∞ :=
  (((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
    ((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias

/-- The honest observer's failure budget at eleven rounds. -/
noncomputable def plonkAttemptFailureBound (actions : ℕ) : ℝ≥0∞ :=
  (((22 * actions + 45 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
    ((148 * actions + 68 : ℕ) : ℝ≥0∞) * challenge255Bias

/-- A common failure budget for the honest law and its public simulator. -/
noncomputable def plonkCommonFailureBound (actions : ℕ) : ℝ≥0∞ :=
  plonkAttemptFailureBound actions + plonkSimulationErrorBound actions

/-- The explicit common budget, keeping both sampling contributions. -/
theorem plonkCommonFailureBound_eq (actions : ℕ) :
    plonkCommonFailureBound actions =
      (((42904 * actions + 4158 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        ((296 * actions + 138 : ℕ) : ℝ≥0∞) * challenge255Bias := by
  simp only [plonkCommonFailureBound, plonkAttemptFailureBound, plonkSimulationErrorBound,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
  ring

/-- Increasing the Action count can only increase this union-bound budget. -/
theorem plonkCommonFailureBound_mono : Monotone plonkCommonFailureBound := by
  intro a b hab
  simp only [plonkCommonFailureBound_eq]
  apply add_le_add
  · exact ENNReal.div_le_div_right (by exact_mod_cast (show 42904 * a + 4158 ≤ 42904 * b + 4158 by omega)) _
  · exact mul_le_mul_left
      (by exact_mod_cast (show 296 * a + 138 ≤ 296 * b + 138 by omega)) _

set_option exponentiation.threshold 1024 in
/-- A kernel arithmetic certificate for positive normalizers, including the one- and two-Action cases. -/
theorem plonkCommonFailureBound_lt_one {actions : ℕ} (hsize : actions ≤ 65535) :
    plonkCommonFailureBound actions < 1 := by
  apply (plonkCommonFailureBound_mono hsize).trans_lt
  rw [plonkCommonFailureBound_eq]
  calc
    _ ≤ (2811717798 : ℝ≥0∞) / scalarFieldOrder + 19398498 * (1 / 2 ^ 260) := by
      change (2811717798 : ℝ≥0∞) / scalarFieldOrder + 19398498 * challenge255Bias ≤ _
      exact add_le_add le_rfl (mul_le_mul_right fieldSample_bias_le 19398498)
    _ < 1 := by
      have hp0 : (scalarFieldOrder : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
      have hpt : (scalarFieldOrder : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
      have hb0 : (2 : ℝ≥0∞) ^ 260 ≠ 0 := pow_ne_zero _ (by simp)
      have hbt : (2 : ℝ≥0∞) ^ 260 ≠ ∞ := ENNReal.pow_ne_top (by simp)
      have hnum : (2811717798 : ℝ≥0∞) * 2 ^ 260 + 19398498 * scalarFieldOrder <
          scalarFieldOrder * 2 ^ 260 := by
        exact_mod_cast (show 2811717798 * 2 ^ 260 + 19398498 * scalarFieldOrder <
          scalarFieldOrder * 2 ^ 260 by decide)
      apply (ENNReal.mul_lt_mul_iff_left hp0 hpt).1
      apply (ENNReal.mul_lt_mul_iff_left hb0 hbt).1
      calc
        _ = ((2811717798 : ℝ≥0∞) / scalarFieldOrder * scalarFieldOrder) * 2 ^ 260 +
            19398498 * scalarFieldOrder * ((1 / 2 ^ 260) * 2 ^ 260) := by ring
        _ = 2811717798 * 2 ^ 260 + 19398498 * scalarFieldOrder := by
          rw [ENNReal.div_mul_cancel hp0 hpt, ENNReal.div_mul_cancel hb0 hbt, mul_one]
        _ < _ := by simpa only [one_mul] using hnum

/-- The conditional comparison pays for both event and normalizer errors. -/
noncomputable def plonkSuccessfulErrorBound (actions : ℕ) : ℝ≥0∞ :=
  2 * plonkSimulationErrorBound actions / (1 - plonkCommonFailureBound actions)

/-- Under the numerical size certificate the conditional denominator is strictly positive. -/
theorem plonkSuccessLowerBound_pos {actions : ℕ} (hsize : actions ≤ 65535) :
    0 < 1 - plonkCommonFailureBound actions :=
  tsub_pos_iff_lt.mpr (plonkCommonFailureBound_lt_one hsize)

end Zcash.Snark.ZeroKnowledge
