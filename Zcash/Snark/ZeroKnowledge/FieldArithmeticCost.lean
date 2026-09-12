import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

/-!
# Explicit field-operation prices

Each operation retains the full costs of its operands and charges the supplied
arithmetic price plus one structural step. Inputs are already costed values;
reading or computing an operand must be charged by its producer. Division uses
the field's total inverse, including at zero, exactly as the protocol does.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Prices for field primitives; representation-specific implementations must justify these prices. -/
structure FieldOperationCosts where
  add : ℕ
  negate : ℕ
  multiply : ℕ
  inverse : ℕ

/-- Add two fully costed operands. -/
def fieldAddCosted {F : Type*} [Add F] (costs : FieldOperationCosts) (left right : F × ℕ) : F × ℕ :=
  (left.1 + right.1, left.2 + right.2 + costs.add + 1)

/-- Addition erasure is the original field addition. -/
theorem fieldAddCosted_result {F : Type*} [Add F] (costs : FieldOperationCosts) (left right : F × ℕ) :
    (fieldAddCosted costs left right).1 = left.1 + right.1 := rfl

/-- Negate a fully costed operand. -/
def fieldNegateCosted {F : Type*} [Neg F] (costs : FieldOperationCosts) (value : F × ℕ) : F × ℕ :=
  (-value.1, value.2 + costs.negate + 1)

/-- Negation erasure is the original field negation. -/
theorem fieldNegateCosted_result {F : Type*} [Neg F] (costs : FieldOperationCosts) (value : F × ℕ) :
    (fieldNegateCosted costs value).1 = -value.1 := rfl

/-- Subtract through the counted negation and addition primitives. -/
def fieldSubtractCosted {F : Type*} [Add F] [Neg F] (costs : FieldOperationCosts)
    (left right : F × ℕ) : F × ℕ :=
  fieldAddCosted costs left (fieldNegateCosted costs right)

/-- Subtraction erasure is the original field subtraction. -/
theorem fieldSubtractCosted_result {F : Type*} [AddGroup F] (costs : FieldOperationCosts)
    (left right : F × ℕ) :
    (fieldSubtractCosted costs left right).1 = left.1 - right.1 := by
  simp only [fieldSubtractCosted, fieldAddCosted_result, fieldNegateCosted_result, sub_eq_add_neg]

/-- Multiply two fully costed operands. -/
def fieldMultiplyCosted {F : Type*} [Mul F] (costs : FieldOperationCosts)
    (left right : F × ℕ) : F × ℕ :=
  (left.1 * right.1, left.2 + right.2 + costs.multiply + 1)

/-- Multiplication erasure is the original field multiplication. -/
theorem fieldMultiplyCosted_result {F : Type*} [Mul F] (costs : FieldOperationCosts)
    (left right : F × ℕ) :
    (fieldMultiplyCosted costs left right).1 = left.1 * right.1 := rfl

/-- Apply the total field inverse with its complete input cost. -/
def fieldInverseCosted {F : Type*} [Inv F] (costs : FieldOperationCosts) (value : F × ℕ) : F × ℕ :=
  (value.1⁻¹, value.2 + costs.inverse + 1)

/-- Inversion erasure agrees even at exceptional zero inputs. -/
theorem fieldInverseCosted_result {F : Type*} [Inv F] (costs : FieldOperationCosts) (value : F × ℕ) :
    (fieldInverseCosted costs value).1 = value.1⁻¹ := rfl

/-- Divide through the counted inverse and multiplication primitives. -/
def fieldDivideCosted {F : Type*} [Mul F] [Inv F] (costs : FieldOperationCosts)
    (left right : F × ℕ) : F × ℕ :=
  fieldMultiplyCosted costs left (fieldInverseCosted costs right)

/-- Division erasure preserves the original totalized field operation. -/
theorem fieldDivideCosted_result {F : Type*} [DivisionMonoid F] (costs : FieldOperationCosts)
    (left right : F × ℕ) :
    (fieldDivideCosted costs left right).1 = left.1 / right.1 := by
  simp only [fieldDivideCosted, fieldMultiplyCosted_result, fieldInverseCosted_result, div_eq_mul_inv]

end Zcash.Snark.ZeroKnowledge
