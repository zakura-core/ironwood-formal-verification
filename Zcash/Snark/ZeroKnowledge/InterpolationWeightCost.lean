import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost
import Zcash.Snark.ZeroKnowledge.ListRoutingCost
import Zcash.Snark.Verifier.Checks

/-!
# Counted interpolation weights

The algorithm executes the verifier's original indexed product, including its
index exclusion and total division at coincident points. List accesses include
the actual traversal, and the supplied evaluation-point cost is retained.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Materialize the exact range, including finite-reader and successor-adapter work. -/
def rangeListCosted (count : ℕ) : List ℕ × ℕ :=
  ofFnCosted (fun index : Fin count => (index.val, 1))

/-- Erasure yields every range index in its original order. -/
theorem rangeListCosted_result (count : ℕ) : (rangeListCosted count).1 = List.range count := by
  simp only [rangeListCosted, ofFnCosted_result]
  apply List.ext_getElem (by simp)
  intro index hleft hright
  simp

/-- The finite range is built with an explicit quadratic adapter bound. -/
theorem rangeListCosted_cost_le (count : ℕ) :
    (rangeListCosted count).2 ≤ count * count + 2 * count + 1 := by
  have h := ofFnCosted_cost_le (fun index : Fin count => (index.val, 1)) 1 (by simp)
  simpa only [rangeListCosted, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- One original interpolation-product step with counted repeated list reads. -/
def interpolationWeightStepCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x pi : F × ℕ) (points : List F) (index : ℕ) (state : F) (other : ℕ) : F × ℕ :=
  if other = index then (state, 1) else
    let pj := getDListCosted read 0 points other
    let numerator := fieldMultiplyCosted costs (state, 1) (fieldSubtractCosted costs x pj)
    let denominator := fieldSubtractCosted costs pi pj
    let result := fieldDivideCosted costs numerator denominator
    (result.1, result.2 + 1)

/-- Both index branches give the exact original product update. -/
theorem interpolationWeightStepCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x pi : F × ℕ) (points : List F) (index : ℕ) (state : F) (other : ℕ) :
    (interpolationWeightStepCosted costs read x pi points index state other).1 =
      if other = index then state
      else state * (x.1 - points.getD other 0) / (pi.1 - points.getD other 0) := by
  unfold interpolationWeightStepCosted
  split <;> simp only [fieldDivideCosted_result, fieldMultiplyCosted_result,
    fieldSubtractCosted_result, getDListCosted_result]

/-- Complete step cost, with no assumption about indices or distinct field points. -/
theorem interpolationWeightStepCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x pi : F × ℕ) (points : List F) (index : ℕ) (state : F) (other : ℕ) :
    (interpolationWeightStepCosted costs read x pi points index state other).2 ≤
      x.2 + pi.2 + 2 * (2 * points.length + read + 1) +
        2 * costs.add + 2 * costs.negate + 2 * costs.multiply + costs.inverse + 12 := by
  have hj := getDListCosted_cost_le read (0 : F) points other
  unfold interpolationWeightStepCosted
  split
  · omega
  · simp only [fieldDivideCosted, fieldMultiplyCosted, fieldSubtractCosted,
      fieldAddCosted, fieldNegateCosted, fieldInverseCosted]
    omega

/-- Execute the verifier's complete interpolation-weight product and build its index list. -/
def interpolationWeightCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x pi : F × ℕ) (points : List F) (index : ℕ) : F × ℕ :=
  let indices := rangeListCosted points.length
  let result := foldlCosted (interpolationWeightStepCosted costs read x pi points index) indices.1 (1, 1)
  (result.1, indices.2 + points.length + result.2 + 1)

/-- The full counted product erases to the inner loop in the original Lagrange evaluator. -/
theorem interpolationWeightCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x pi : F × ℕ) (points : List F) (index : ℕ) :
    (interpolationWeightCosted costs read x pi points index).1 =
      (List.range points.length).foldl (fun state other =>
        if other = index then state
        else state * (x.1 - points.getD other 0) / (pi.1 - points.getD other 0)) 1 := by
  simp only [interpolationWeightCosted, foldlCosted_result, interpolationWeightStepCosted_result,
    rangeListCosted_result]

/-- Complete interpolation-weight bound from the actual point-list length and input-reader cost. -/
def interpolationWeightCostBudget (costs : FieldOperationCosts) (read count pointAccess : ℕ) : ℕ :=
  count * count + count * (pointAccess + 3 * (2 * count + read + 1) +
    2 * costs.add + 2 * costs.negate + 2 * costs.multiply + costs.inverse + 20) + 10

/-- The cost bound includes index-list construction, length reads, and every product step. -/
theorem interpolationWeightCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x pi : F × ℕ) (points : List F) (index : ℕ)
    (hpi : pi.2 ≤ 2 * points.length + read + 1) :
    (interpolationWeightCosted costs read x pi points index).2 ≤
      interpolationWeightCostBudget costs read points.length x.2 := by
  let stepBudget := x.2 + pi.2 + 2 * (2 * points.length + read + 1) +
    2 * costs.add + 2 * costs.negate + 2 * costs.multiply + costs.inverse + 12
  have hfold := foldlCosted_cost_le_sum (interpolationWeightStepCosted costs read x pi points index)
    (rangeListCosted points.length).1 (1, 1) (fun _ => True) (fun _ => stepBudget)
    trivial (fun _ _ _ _ => trivial) (fun state _ other _ =>
      interpolationWeightStepCosted_cost_le costs read x pi points index state other)
  have hindices := rangeListCosted_cost_le points.length
  have hsize : (rangeListCosted points.length).1.length = points.length := by
    rw [rangeListCosted_result, List.length_range]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, hsize] at hfold
  have hstep : stepBudget ≤ x.2 + 3 * (2 * points.length + read + 1) +
      2 * costs.add + 2 * costs.negate + 2 * costs.multiply + costs.inverse + 12 := by
    dsimp only [stepBudget]
    omega
  have hscaled := Nat.mul_le_mul_left points.length hstep
  simp only [interpolationWeightCosted, interpolationWeightCostBudget]
  nlinarith

end Zcash.Snark.ZeroKnowledge
