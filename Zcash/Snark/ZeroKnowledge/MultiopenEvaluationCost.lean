import Zcash.Snark.ZeroKnowledge.LagrangeEvaluationCost

/-!
# Counted multi-opening evaluation

The full original interpolant, denominator product, and ordered set fold are
executed with their costs. Materialized point and evaluation lists carry their
actual lengths; challenge and claim inputs retain complete supplied costs.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- One denominator-product step, retaining the point read and total field inverse. -/
def multiopenDenominatorStepCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (state point : F) : F × ℕ :=
  fieldMultiplyCosted costs (state, 1)
    (fieldInverseCosted costs (fieldSubtractCosted costs x (point, read + 1)))

/-- The counted denominator update matches the original formula, even when the factor is zero. -/
theorem multiopenDenominatorStepCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (state point : F) :
    (multiopenDenominatorStepCosted costs read x state point).1 = state * (x.1 - point)⁻¹ := by
  simp only [multiopenDenominatorStepCosted, fieldMultiplyCosted_result,
    fieldInverseCosted_result, fieldSubtractCosted_result]

/-- Every point-read, subtraction, inverse, and product is counted. -/
theorem multiopenDenominatorStepCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (state point : F) :
    (multiopenDenominatorStepCosted costs read x state point).2 ≤
      x.2 + read + costs.add + costs.negate + costs.inverse + costs.multiply + 8 := by
  simp only [multiopenDenominatorStepCosted, fieldMultiplyCosted, fieldInverseCosted,
    fieldSubtractCosted, fieldAddCosted, fieldNegateCosted]
  omega

/-- Evaluate one complete point-set quotient, including interpolation and every denominator. -/
def multiopenSetEvalCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) (claim : F × ℕ) : F × ℕ :=
  let interpolant := lagrangeEvalCosted costs read x points evals
  let initial := fieldSubtractCosted costs claim interpolant
  foldlCosted (multiopenDenominatorStepCosted costs read x) points initial

/-- One set erases to the original interpolant subtraction and denominator-product fold. -/
theorem multiopenSetEvalCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) (claim : F × ℕ) :
    (multiopenSetEvalCosted costs read x points evals claim).1 =
      points.foldl (fun state point => state * (x.1 - point)⁻¹)
        (claim.1 - lagrangeEval x.1 points evals) := by
  simp only [multiopenSetEvalCosted, foldlCosted_result, multiopenDenominatorStepCosted_result,
    fieldSubtractCosted_result, lagrangeEvalCosted_result]

/-- Complete per-set budget in actual input lengths and complete challenge and claim costs. -/
def multiopenSetEvalCostBudget (costs : FieldOperationCosts)
    (read points evals pointAccess claimAccess : ℕ) : ℕ :=
  claimAccess + lagrangeEvalCostBudget costs read points evals pointAccess + costs.add + costs.negate +
    points * (pointAccess + read + costs.add + costs.negate + costs.inverse + costs.multiply + 9) + 5

/-- The set budget pays for interpolation and the entire denominator loop. -/
theorem multiopenSetEvalCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x : F × ℕ) (points evals : List F) (claim : F × ℕ) :
    (multiopenSetEvalCosted costs read x points evals claim).2 ≤
      multiopenSetEvalCostBudget costs read points.length evals.length x.2 claim.2 := by
  have hinterpolant := lagrangeEvalCosted_cost_le costs read x points evals
  let initial := fieldSubtractCosted costs claim (lagrangeEvalCosted costs read x points evals)
  let stepBudget := x.2 + read + costs.add + costs.negate + costs.inverse + costs.multiply + 8
  have hfold := foldlCosted_cost_le_sum (multiopenDenominatorStepCosted costs read x) points initial
    (fun _ => True) (fun _ => stepBudget) trivial (fun _ _ _ _ => trivial)
    (fun state _ point _ => multiopenDenominatorStepCosted_cost_le costs read x state point)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hfold
  have hinitial : initial.2 ≤ claim.2 + lagrangeEvalCostBudget costs read points.length evals.length x.2 +
      costs.add + costs.negate + 2 := by
    simp only [initial, fieldSubtractCosted, fieldAddCosted, fieldNegateCosted]
    omega
  dsimp only [stepBudget] at hfold
  change (foldlCosted (multiopenDenominatorStepCosted costs read x) points initial).2 ≤ _
  unfold multiopenSetEvalCostBudget
  nlinarith

/-- Combine one complete quotient evaluation with the accumulated multi-opening claim. -/
def multiopenEvalStepCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x2 x3 : F × ℕ) (state : F) (entry : List F × List F × (F × ℕ)) : F × ℕ :=
  fieldAddCosted costs (fieldMultiplyCosted costs (state, 1) x2)
    (multiopenSetEvalCosted costs read x3 entry.1 entry.2.1 entry.2.2)

/-- Count the original ordered fold over every point set. -/
def multiopenEvalCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x2 x3 : F × ℕ) (sets : List (List F × List F × (F × ℕ))) : F × ℕ :=
  foldlCosted (multiopenEvalStepCosted costs read x2 x3) sets (0, 1)

/-- The complete counted multi-opening evaluator erases to the actual verifier calculation. -/
theorem multiopenEvalCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x2 x3 : F × ℕ) (sets : List (List F × List F × (F × ℕ))) :
    (multiopenEvalCosted costs read x2 x3 sets).1 =
      multiopenEval x2.1 x3.1 (sets.map (fun entry => (entry.1, entry.2.1, entry.2.2.1))) := by
  simp only [multiopenEvalCosted, foldlCosted_result, multiopenEvalStepCosted,
    fieldAddCosted_result, fieldMultiplyCosted_result, multiopenSetEvalCosted_result,
    multiopenEval, List.foldl_map]

/-- Actual input sizes give a complete aggregate budget, including the final ordered fold. -/
def multiopenEvalCostBudget {F : Type*} (costs : FieldOperationCosts)
    (read x2Access x3Access : ℕ) (sets : List (List F × List F × (F × ℕ))) : ℕ :=
  (sets.map (fun entry => multiopenSetEvalCostBudget costs read entry.1.length entry.2.1.length
    x3Access entry.2.2.2 + x2Access + costs.multiply + costs.add + 4)).sum + sets.length + 2

/-- Every point-set calculation and challenge access is included in the full evaluator bound. -/
theorem multiopenEvalCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (read : ℕ) (x2 x3 : F × ℕ) (sets : List (List F × List F × (F × ℕ))) :
    (multiopenEvalCosted costs read x2 x3 sets).2 ≤
      multiopenEvalCostBudget costs read x2.2 x3.2 sets := by
  let budget := fun entry : List F × List F × (F × ℕ) =>
    multiopenSetEvalCostBudget costs read entry.1.length entry.2.1.length x3.2 entry.2.2.2 +
      x2.2 + costs.multiply + costs.add + 4
  have h := foldlCosted_cost_le_sum (multiopenEvalStepCosted costs read x2 x3) sets (0, 1)
    (fun _ => True) budget trivial (fun _ _ _ _ => trivial) (fun state _ entry _ => by
      have hset := multiopenSetEvalCosted_cost_le costs read x3 entry.1 entry.2.1 entry.2.2
      dsimp only [multiopenEvalStepCosted, fieldAddCosted, fieldMultiplyCosted, budget]
      omega)
  change (foldlCosted (multiopenEvalStepCosted costs read x2 x3) sets (0, 1)).2 ≤
    (sets.map budget).sum + sets.length + 2
  calc
    _ ≤ 1 + (sets.map budget).sum + sets.length + 1 := h
    _ = _ := by omega

end Zcash.Snark.ZeroKnowledge
