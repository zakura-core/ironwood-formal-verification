import Zcash.Snark.ZeroKnowledge.OracleBitBounds

/-!
# A uniform budget for indefinitely many shared-oracle comparisons

For a retry rate at most one half and cache growth at most twenty-two per
attempt, `2 * Gamma(m, q + 22)` is a comparison potential. This deliberately
simple bound avoids taking the divergent limit of the earlier bound that
charged every available attempt. It does not by itself assert termination.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

/-- Twenty-two further cached queries suffice to pay the geometrically weighted future losses. -/
noncomputable def oracleRetryPotential (actions queries : ℕ) : ℝ≥0∞ :=
  2 * plonkBitSimulationErrorBound actions (queries + 22)

/-- The potential is twice the one-attempt error plus forty-four inverse-field-order terms. -/
theorem oracleRetryPotential_eq (actions queries : ℕ) :
    oracleRetryPotential actions queries =
      2 * (plonkBitSimulationErrorBound actions queries + 22 / scalarFieldOrder) := by
  simp only [oracleRetryPotential, plonkBitSimulationErrorBound, Nat.cast_add,
    Nat.cast_ofNat, div_eq_mul_inv]
  ring

/-- Increasing the prior cache budget cannot decrease the potential. -/
theorem oracleRetryPotential_mono_queries (actions : ℕ) {left right : ℕ} (h : left ≤ right) :
    oracleRetryPotential actions left ≤ oracleRetryPotential actions right :=
  mul_le_mul_right (plonkBitSimulationErrorBound_mono_queries actions (Nat.add_le_add_right h 22)) 2

/-- The potential pays the next comparison and the retry-weighted continuation in every state. -/
theorem oracleRetryPotential_step (actions queries : ℕ) {rate : ℝ≥0∞}
    (hrate : rate ≤ 1 / 2) :
    plonkBitSimulationErrorBound actions queries + rate * oracleRetryPotential actions (queries + 22) ≤
      oracleRetryPotential actions queries := by
  apply (add_le_add le_rfl (mul_le_mul_left hrate _)).trans_eq
  rw [oracleRetryPotential, ← mul_assoc]
  have hhalf : (1 / 2 : ℝ≥0∞) * 2 = 1 := ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  rw [hhalf, one_mul]
  simp only [oracleRetryPotential, plonkBitSimulationErrorBound, Nat.cast_add,
    Nat.cast_ofNat, div_eq_mul_inv]
  ring

/-- The readable potential bound retains the initial-cache and future-cache costs separately. -/
theorem oracleRetryPotential_binary_lt {actions : ℕ} (hpositive : 1 ≤ actions) (queries : ℕ) :
    oracleRetryPotential actions queries <
      2 * (actions * (1 / (2 : ℝ≥0∞) ^ 238) + (queries + 22 : ℕ) / scalarFieldOrder) := by
  exact (ENNReal.mul_lt_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).2
      (plonkBitSimulationErrorBound_lt_actions_mul_two_pow hpositive (queries + 22))

end Zcash.Snark.ZeroKnowledge
