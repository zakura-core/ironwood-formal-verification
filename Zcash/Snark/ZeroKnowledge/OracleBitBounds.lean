import Zcash.Snark.ZeroKnowledge.PlonkBinaryBounds

/-!
# Error budget for the simulator with a fixed bit tape

Wide reduction of the simulator's `132m + 36` private fields adds that many bias
terms to the existing oracle comparison. This gives
`(42882m + 4113 + q) / p + (280m + 106) delta`. The extra terms describe a new
simulator distribution; the earlier ideal-field simulator keeps its sharper
bound. The conservative binary bound remains `m * 2^-238 + q / p`.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- The complete budget when both the real prover and the simulator reduce finite raw-word tapes. -/
noncomputable def plonkBitSimulationErrorBound (actions queries : ℕ) : ℝ≥0∞ :=
  plonkSimulationErrorBound actions + (132 * actions + 36 : ℕ) * challenge255Bias +
    (queries : ℝ≥0∞) / scalarFieldOrder

/-- Combining the two private-tape costs gives the explicit bit-simulator formula. -/
theorem plonkBitSimulationErrorBound_expanded (actions queries : ℕ) :
    plonkBitSimulationErrorBound actions queries =
      ((42882 * actions + 4113 + queries : ℕ) : ℝ≥0∞) / scalarFieldOrder +
        (280 * actions + 106 : ℕ) * challenge255Bias := by
  unfold plonkBitSimulationErrorBound plonkSimulationErrorBound
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
  ring

/-- Prior oracle queries contribute their separate inverse-field-order term. -/
theorem plonkBitSimulationErrorBound_queries (actions queries : ℕ) :
    plonkBitSimulationErrorBound actions queries =
      plonkBitSimulationErrorBound actions 0 + (queries : ℝ≥0∞) / scalarFieldOrder := by
  simp only [plonkBitSimulationErrorBound, Nat.cast_zero, ENNReal.zero_div, add_zero]

/-- A bound on preprocessing queries can replace the actual prior cache length. -/
theorem plonkBitSimulationErrorBound_mono_queries (actions : ℕ) {left right : ℕ}
    (hle : left ≤ right) :
    plonkBitSimulationErrorBound actions left ≤ plonkBitSimulationErrorBound actions right := by
  unfold plonkBitSimulationErrorBound
  apply add_le_add le_rfl
  apply ENNReal.div_le_div_right
  exact_mod_cast hle

/-- The constant part of the added simulator bias is charged at most once per Action. -/
theorem plonkBitSimulationErrorBound_le_actions_mul_one {actions : ℕ} (hsize : 1 ≤ actions) :
    plonkBitSimulationErrorBound actions 0 ≤ actions * plonkBitSimulationErrorBound 1 0 := by
  simp only [plonkBitSimulationErrorBound, Nat.cast_zero, ENNReal.zero_div, add_zero]
  change plonkSimulationErrorBound actions + ((132 * actions + 36 : ℕ) : ℝ≥0∞) * challenge255Bias ≤
    actions * (plonkSimulationErrorBound 1 + 168 * challenge255Bias)
  calc
    _ ≤ actions * plonkSimulationErrorBound 1 + (actions * 168 : ℝ≥0∞) * challenge255Bias := by
      apply add_le_add (plonkSimulationErrorBound_le_actions_mul_one hsize)
      apply mul_le_mul_left
      exact_mod_cast (show 132 * actions + 36 ≤ actions * 168 by omega)
    _ = _ := by ring

set_option exponentiation.threshold 1024 in
/-- Even the simulator's added sampling bias leaves the one-Action zero-prior-query budget below 2^-238. -/
theorem plonkBitSimulationErrorBound_one_lt_two_pow :
    plonkBitSimulationErrorBound 1 0 < 1 / (2 : ℝ≥0∞) ^ 238 := by
  rw [plonkBitSimulationErrorBound_expanded]
  change (46995 : ℝ≥0∞) / scalarFieldOrder + 386 * challenge255Bias < _
  calc
    _ ≤ (46995 : ℝ≥0∞) / scalarFieldOrder + 386 * (1 / 2 ^ 260) :=
      add_le_add le_rfl (mul_le_mul_right fieldSample_bias_le 386)
    _ < 1 / 2 ^ 238 := by
      have hp0 : (scalarFieldOrder : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
      have hpt : (scalarFieldOrder : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
      have hb0 : (2 : ℝ≥0∞) ^ 260 ≠ 0 := pow_ne_zero _ (by simp)
      have hbt : (2 : ℝ≥0∞) ^ 260 ≠ ∞ := ENNReal.pow_ne_top (by simp)
      have ht0 : (2 : ℝ≥0∞) ^ 238 ≠ 0 := pow_ne_zero _ (by simp)
      have htt : (2 : ℝ≥0∞) ^ 238 ≠ ∞ := ENNReal.pow_ne_top (by simp)
      have hnum : ((46995 : ℝ≥0∞) * 2 ^ 260 + 386 * scalarFieldOrder) * 2 ^ 238 <
          scalarFieldOrder * 2 ^ 260 := by
        exact_mod_cast (show (46995 * 2 ^ 260 + 386 * scalarFieldOrder) * 2 ^ 238 <
          scalarFieldOrder * 2 ^ 260 by decide)
      apply (ENNReal.mul_lt_mul_iff_left ht0 htt).1
      apply (ENNReal.mul_lt_mul_iff_left hp0 hpt).1
      apply (ENNReal.mul_lt_mul_iff_left hb0 hbt).1
      calc
        _ = ((46995 / (scalarFieldOrder : ℝ≥0∞) * scalarFieldOrder) * 2 ^ 260 +
            386 * scalarFieldOrder * ((1 / 2 ^ 260) * 2 ^ 260)) * 2 ^ 238 := by ring
        _ = (46995 * 2 ^ 260 + 386 * scalarFieldOrder) * 2 ^ 238 := by
          rw [ENNReal.div_mul_cancel hp0 hpt, ENNReal.div_mul_cancel hb0 hbt, mul_one]
        _ < scalarFieldOrder * 2 ^ 260 := hnum
        _ = _ := by rw [ENNReal.div_mul_cancel ht0 htt, one_mul]

/-- A positive Action count retains the same readable binary bound plus the prior-query cost. -/
theorem plonkBitSimulationErrorBound_lt_actions_mul_two_pow {actions : ℕ} (hsize : 1 ≤ actions)
    (queries : ℕ) :
    plonkBitSimulationErrorBound actions queries <
      actions * (1 / (2 : ℝ≥0∞) ^ 238) + (queries : ℝ≥0∞) / scalarFieldOrder := by
  have ha0 : (actions : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hat : (actions : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hzero := (plonkBitSimulationErrorBound_le_actions_mul_one hsize).trans_lt
    ((ENNReal.mul_lt_mul_iff_right ha0 hat).2 plonkBitSimulationErrorBound_one_lt_two_pow)
  rw [plonkBitSimulationErrorBound_queries]
  exact ENNReal.add_lt_add_right
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.mpr (NeZero.ne _))) hzero

end Zcash.Snark.ZeroKnowledge
