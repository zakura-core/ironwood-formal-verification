import Zcash.Snark.ZeroKnowledge.InterpolationWeightCost

/-!
# Counted complete Lagrange evaluation

Both indexed loops use the original materialized point and evaluation lists.
The bound pays for repeated list traversals and every arithmetic operation,
including the original out-of-range defaults and coincident-point behavior.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- One complete interpolation summand, retaining the weight calculation and evaluation read. -/
def lagrangeSummandStepCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) (state : F) (index : ℕ) : F × ℕ :=
  let pi := getDListCosted read 0 points index
  let weight := interpolationWeightCosted costs read x pi points index
  let evaluation := getDListCosted read 0 evals index
  fieldAddCosted costs (state, 1) (fieldMultiplyCosted costs evaluation weight)

/-- The counted summand equals the original nested-loop update at every index. -/
theorem lagrangeSummandStepCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) (state : F) (index : ℕ) :
    (lagrangeSummandStepCosted costs read x points evals state index).1 =
      state + evals.getD index 0 * ((List.range points.length).foldl (fun product other =>
        if other = index then product
        else product * (x.1 - points.getD other 0) /
          (points.getD index 0 - points.getD other 0)) 1) := by
  simp only [lagrangeSummandStepCosted, fieldAddCosted_result, fieldMultiplyCosted_result,
    interpolationWeightCosted_result, getDListCosted_result]

/-- Summand cost includes all repeated point reads and the complete interpolation weight. -/
theorem lagrangeSummandStepCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) (state : F) (index : ℕ) :
    (lagrangeSummandStepCosted costs read x points evals state index).2 ≤
      interpolationWeightCostBudget costs read points.length x.2 +
        2 * evals.length + read + costs.add + costs.multiply + 8 := by
  have hpi := getDListCosted_cost_le read (0 : F) points index
  have heval := getDListCosted_cost_le read (0 : F) evals index
  have hweight := interpolationWeightCosted_cost_le costs read x
    (getDListCosted read 0 points index) points index hpi
  simp only [lagrangeSummandStepCosted, fieldAddCosted, fieldMultiplyCosted]
  omega

/-- Execute and count both loops of the original complete Lagrange evaluation. -/
def lagrangeEvalCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) : F × ℕ :=
  let indices := rangeListCosted points.length
  let result := foldlCosted (lagrangeSummandStepCosted costs read x points evals) indices.1 (0, 1)
  (result.1, indices.2 + points.length + result.2 + 1)

/-- Erasure is the verifier's actual Lagrange evaluator, including exceptional inputs. -/
theorem lagrangeEvalCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) :
    (lagrangeEvalCosted costs read x points evals).1 = lagrangeEval x.1 points evals := by
  simp only [lagrangeEvalCosted, foldlCosted_result, lagrangeSummandStepCosted_result,
    rangeListCosted_result, lagrangeEval]

/-- Explicit bound in the actual stored point and evaluation lengths and point-access cost. -/
def lagrangeEvalCostBudget (costs : FieldOperationCosts) (read points evals pointAccess : ℕ) : ℕ :=
  points * points + points * (interpolationWeightCostBudget costs read points pointAccess +
    2 * evals + read + costs.add + costs.multiply + 14) + 10

/-- The complete evaluator bound retains both loop constructions, all accesses, and arithmetic. -/
theorem lagrangeEvalCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) :
    (lagrangeEvalCosted costs read x points evals).2 ≤
      lagrangeEvalCostBudget costs read points.length evals.length x.2 := by
  let stepBudget := interpolationWeightCostBudget costs read points.length x.2 +
    2 * evals.length + read + costs.add + costs.multiply + 8
  have hfold := foldlCosted_cost_le_sum (lagrangeSummandStepCosted costs read x points evals)
    (rangeListCosted points.length).1 (0, 1) (fun _ => True) (fun _ => stepBudget)
    trivial (fun _ _ _ _ => trivial) (fun state _ index _ =>
      lagrangeSummandStepCosted_cost_le costs read x points evals state index)
  have hindices := rangeListCosted_cost_le points.length
  have hsize : (rangeListCosted points.length).1.length = points.length := by
    rw [rangeListCosted_result, List.length_range]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, hsize] at hfold
  dsimp only [stepBudget] at hfold
  simp only [lagrangeEvalCosted, lagrangeEvalCostBudget]
  nlinarith

end Zcash.Snark.ZeroKnowledge
