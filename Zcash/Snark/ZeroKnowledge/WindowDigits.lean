import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Canonical three-bit witness windows

These elementary identities connect the circuit's bit-window program to an
exact scalar decomposition. They concern application witnesses, independently
of the prover's blinding randomness and its statistical sampling bound.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The circuit's shift-and-mask window is exactly the corresponding base-eight digit. -/
theorem octalDigit_eq_shift_mask (value window : ℕ) :
    value / 8 ^ window % 8 = (value >>> (3 * window)) &&& 7 := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  simpa only [show (2 : ℕ) ^ 3 = 8 from rfl, show (2 : ℕ) ^ 3 - 1 = 7 from rfl] using
    (Nat.and_two_pow_sub_one_eq_mod (value / 8 ^ window) 3).symm

/-- Reassembling a fixed number of base-eight digits gives the exact low-window residue. -/
theorem octalDigits_sum_mod (value count : ℕ) :
    (∑ window ∈ Finset.range count, (value / 8 ^ window % 8) * 8 ^ window) = value % 8 ^ count := by
  induction count with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, pow_zero, Nat.mod_one]
  | succ count ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
    ac_rfl

end Zcash.Snark.ZeroKnowledge
