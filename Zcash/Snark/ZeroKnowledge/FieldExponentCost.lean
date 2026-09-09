import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost

/-!
# Counted field casts and signed powers

Natural casts execute an addition loop. Signed powers execute the existing
counted multiplication loop and, for negative exponents, one total field inverse.
Both branches retain the complete base-access cost, including at zero.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Construct a natural field constant by an explicit counted addition loop. -/
def fieldNatCastCosted {F : Type*} [AddMonoidWithOne F] (add : ℕ) : ℕ → F × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let previous := fieldNatCastCosted add n
    (previous.1 + 1, previous.2 + add + 1)

/-- Erasing the counter gives the original natural cast. -/
theorem fieldNatCastCosted_result {F : Type*} [AddMonoidWithOne F] (add n : ℕ) :
    (fieldNatCastCosted (F := F) add n).1 = (n : F) := by
  induction n with
  | zero => simp [fieldNatCastCosted]
  | succ n ih => simp only [fieldNatCastCosted, ih, Nat.cast_add, Nat.cast_one]

/-- Exact cost of constructing the field constant. -/
theorem fieldNatCastCosted_cost {F : Type*} [AddMonoidWithOne F] (add n : ℕ) :
    (fieldNatCastCosted (F := F) add n).2 = n * (add + 1) + 1 := by
  induction n with
  | zero => simp [fieldNatCastCosted]
  | succ n ih => simp only [fieldNatCastCosted, ih, Nat.add_mul, Nat.one_mul]; omega

/-- Compute a signed power and retain the full cost of reading the base. -/
def fieldIntegerPowerCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (base : F × ℕ) : ℤ → F × ℕ
  | .ofNat n =>
    let power := fieldPowerCosted costs.multiply base.1 n
    (power.1, base.2 + power.2 + 1)
  | .negSucc n =>
    let power := fieldPowerCosted costs.multiply base.1 (n + 1)
    (power.1⁻¹, base.2 + power.2 + costs.inverse + 1)

/-- Erasure is the original total signed power, including a zero base. -/
theorem fieldIntegerPowerCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (base : F × ℕ) (exponent : ℤ) :
    (fieldIntegerPowerCosted costs base exponent).1 = base.1 ^ exponent := by
  cases exponent <;> simp [fieldIntegerPowerCosted, fieldPowerCosted_result, zpow_negSucc]

/-- Both signs fit the same magnitude-dependent bound with an explicit inverse price. -/
theorem fieldIntegerPowerCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (base : F × ℕ) (exponent : ℤ) :
    (fieldIntegerPowerCosted costs base exponent).2 ≤
      base.2 + exponent.natAbs * (costs.multiply + 1) + costs.inverse + 2 := by
  cases exponent <;>
    simp only [fieldIntegerPowerCosted, fieldPowerCosted_cost, Int.natAbs, Nat.succ_eq_add_one] <;>
    omega

end Zcash.Snark.ZeroKnowledge
