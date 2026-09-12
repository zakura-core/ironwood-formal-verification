import Zcash.Snark.ZeroKnowledge.StatefulRetrySimulation
import Zcash.Snark.ZeroKnowledge.OracleBitBounds

/-!
# Finite shared-oracle retry error

Each attempted proof can add twenty-two cache entries. For `n` attempts the
conservative comparison is `n * epsilon_bits(m, q) + 11n(n-1)/p`. It charges
every possible attempt, without assuming independent retry decisions or a
geometric tail for a shared random oracle.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

/-- Full bit-simulator comparison and all possible preceding oracle entries across finite retries. -/
noncomputable def oracleRetryError (actions queries attempts : ℕ) : ℝ≥0∞ :=
  attempts * plonkBitSimulationErrorBound actions 0 +
    ((attempts * queries + 11 * attempts * (attempts - 1) : ℕ) : ℝ≥0∞) / scalarFieldOrder

/-- A zero attempt budget produces the same explicit empty exhausted history on both sides. -/
theorem oracleRetryError_zero (actions queries : ℕ) : oracleRetryError actions queries 0 = 0 := by
  simp [oracleRetryError]

/-- The cost of one attempt plus the continuation with twenty-two more possible cache entries. -/
theorem oracleRetryError_succ (actions queries attempts : ℕ) :
    oracleRetryError actions queries (attempts + 1) =
      plonkBitSimulationErrorBound actions queries + oracleRetryError actions (queries + 22) attempts := by
  rw [plonkBitSimulationErrorBound_queries actions queries]
  cases attempts with
  | zero => simp [oracleRetryError]
  | succ attempts =>
    simp only [oracleRetryError, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
    ring

/-- The closed formula is exactly the state-dependent hybrid's recurrence. -/
theorem oracleRetryError_eq_stateful (actions queries attempts : ℕ) :
    statefulRetryError (plonkBitSimulationErrorBound actions) 22 queries attempts =
      oracleRetryError actions queries attempts := by
  induction attempts generalizing queries with
  | zero => simp [statefulRetryError, oracleRetryError_zero]
  | succ attempts ih => rw [statefulRetryError, ih, oracleRetryError_succ]

/-- Separate the repeated one-attempt error from the cost of cache entries introduced by earlier retries. -/
theorem oracleRetryError_eq_mul (actions queries attempts : ℕ) :
    oracleRetryError actions queries attempts =
      attempts * plonkBitSimulationErrorBound actions queries +
        ((11 * attempts * (attempts - 1) : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
  rw [plonkBitSimulationErrorBound_queries actions queries]
  simp only [oracleRetryError, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
  ring

/-- More preprocessing queries can only increase the shared-oracle budget. -/
theorem oracleRetryError_mono_queries (actions attempts : ℕ) {left right : ℕ} (h : left ≤ right) :
    oracleRetryError actions left attempts ≤ oracleRetryError actions right attempts := by
  rw [oracleRetryError_eq_mul, oracleRetryError_eq_mul]
  exact add_le_add (mul_le_mul_right (plonkBitSimulationErrorBound_mono_queries actions h) attempts) le_rfl

/-- A readable bound for arbitrary finite attempt budgets, without a shared-oracle termination assumption. -/
theorem oracleRetryError_binary_le {actions : ℕ} (hsize : 1 ≤ actions) (queries attempts : ℕ) :
    oracleRetryError actions queries attempts ≤
      (attempts * actions : ℝ≥0∞) * (1 / (2 : ℝ≥0∞) ^ 238) +
        ((attempts * queries + 11 * attempts * (attempts - 1) : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
  have h := (plonkBitSimulationErrorBound_lt_actions_mul_two_pow hsize 0).le
  simp only [Nat.cast_zero, ENNReal.zero_div, add_zero] at h
  exact add_le_add (by simpa only [mul_assoc] using mul_le_mul_right h attempts) le_rfl

end Zcash.Snark.ZeroKnowledge
