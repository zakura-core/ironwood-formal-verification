import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost
import Zcash.Snark.Verifier.Expressions

/-!
# Counted folding of the verifier's quotient evaluation

The complete expression list is folded in the original order and divided by the
same totalized vanishing value. Each materialized expression and challenge keeps
its complete access cost. No off-domain or nonzero-denominator premise is used.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Count an ordered field Horner fold over materialized, fully costed values. -/
def fieldHornerFoldCosted {F : Type*} [Semiring F] (costs : FieldOperationCosts)
    (challenge : F × ℕ) (values : List (F × ℕ)) : F × ℕ :=
  foldlCosted (fun state value =>
    (state * challenge.1 + value.1, challenge.2 + value.2 + costs.multiply + costs.add + 1)) values (0, 1)

/-- The counted fold has the exact original ordered scalar value. -/
theorem fieldHornerFoldCosted_result {F : Type*} [Semiring F] (costs : FieldOperationCosts)
    (challenge : F × ℕ) (values : List (F × ℕ)) :
    (fieldHornerFoldCosted costs challenge values).1 =
      (values.map Prod.fst).foldl (fun state value => state * challenge.1 + value) 0 := by
  simp only [fieldHornerFoldCosted, foldlCosted_result, List.foldl_map]

/-- All Horner arithmetic and supplied element accesses are retained. -/
theorem fieldHornerFoldCosted_cost_le {F : Type*} [Semiring F] (costs : FieldOperationCosts)
    (challenge : F × ℕ) (values : List (F × ℕ)) (access : ℕ)
    (hread : ∀ value ∈ values, value.2 ≤ access) :
    (fieldHornerFoldCosted costs challenge values).2 ≤
      values.length * (challenge.2 + access + costs.multiply + costs.add + 2) + 2 := by
  have h := foldlCosted_cost_le_sum (fun state (value : F × ℕ) =>
      (state * challenge.1 + value.1, challenge.2 + value.2 + costs.multiply + costs.add + 1))
    values (0, 1) (fun _ => True) (fun _ => challenge.2 + access + costs.multiply + costs.add + 1)
    trivial (fun _ _ _ _ => trivial) (fun _ _ value hvalue => by
      have hr := hread value hvalue
      dsimp only
      omega)
  have hsum : (values.map (fun _ => challenge.2 + access + costs.multiply + costs.add + 1)).sum =
      values.length * (challenge.2 + access + costs.multiply + costs.add + 1) := by simp
  rw [hsum] at h
  dsimp only [fieldHornerFoldCosted]
  calc
    _ ≤ 1 + values.length * (challenge.2 + access + costs.multiply + costs.add + 1) + values.length + 1 := h
    _ = _ := by ring

/-- Execute the original quotient-evaluation fold and total inverse with their complete costs. -/
def expectedHEvalCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (expressions : List (F × ℕ)) (y xn : F × ℕ) : F × ℕ :=
  fieldMultiplyCosted costs (fieldHornerFoldCosted costs y expressions)
    (fieldInverseCosted costs (fieldSubtractCosted costs xn (1, 1)))

/-- Erasure equals the verifier's actual inferred quotient value at every challenge. -/
theorem expectedHEvalCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (expressions : List (F × ℕ)) (y xn : F × ℕ) :
    (expectedHEvalCosted costs expressions y xn).1 = expectedHEval (expressions.map Prod.fst) y.1 xn.1 := by
  simp only [expectedHEvalCosted, fieldMultiplyCosted_result, fieldHornerFoldCosted_result,
    fieldInverseCosted_result, fieldSubtractCosted_result, expectedHEval]

/-- Complete quotient-evaluation cost, including a zero vanishing denominator. -/
theorem expectedHEvalCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (expressions : List (F × ℕ)) (y xn : F × ℕ) (access : ℕ)
    (hread : ∀ value ∈ expressions, value.2 ≤ access) :
    (expectedHEvalCosted costs expressions y xn).2 ≤
      expressions.length * (y.2 + access + costs.multiply + costs.add + 2) +
        xn.2 + costs.add + costs.negate + costs.multiply + costs.inverse + 8 := by
  have hfold := fieldHornerFoldCosted_cost_le costs y expressions access hread
  dsimp only [expectedHEvalCosted, fieldMultiplyCosted, fieldInverseCosted,
    fieldSubtractCosted, fieldAddCosted, fieldNegateCosted]
  omega

end Zcash.Snark.ZeroKnowledge
