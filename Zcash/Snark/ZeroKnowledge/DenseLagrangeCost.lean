import Zcash.Snark.ZeroKnowledge.LagrangePolynomialTotal
import Zcash.Snark.ZeroKnowledge.LagrangeEvaluationCost
import Zcash.Snark.ZeroKnowledge.DenseRowPolynomial
import Zcash.Snark.ZeroKnowledge.CosetPolynomial

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp omegaOf)

/-- Evaluate the indexed interpolant at an internally constructed domain point with all work counted. -/
def denseLagrangeNodeCosted (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (points evals : List Fp) (index : Fin (2 ^ k)) : Fp × ℕ :=
  let power := fieldPowerCosted costs.multiply (omegaOf k) index.val
  let value := lagrangeEvalCosted costs read (power.1, 1) points evals
  (value.1, omegaAccess + power.2 + value.2 + 2)

/-- The counted value is the original interpolation polynomial at that domain point, including repeated nodes. -/
theorem denseLagrangeNodeCosted_result (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (points evals : List Fp) (index : Fin (2 ^ k)) :
    (denseLagrangeNodeCosted costs read omegaAccess k points evals index).1 =
      (lagrangePoly points evals).eval (omegaOf k ^ index.val) := by
  simp only [denseLagrangeNodeCosted, lagrangeEvalCosted_result, fieldPowerCosted_result,
    lagrangePoly_eval_total]

/-- Uniform complete budget for an interpolation-domain value. -/
def denseLagrangeNodeCostBudget (costs : FieldOperationCosts) (read omegaAccess k points evals : ℕ) : ℕ :=
  omegaAccess + 2 ^ k * (costs.multiply + 1) + lagrangeEvalCostBudget costs read points evals 1 + 3

/-- Constructing the point and running both interpolation loops are included in the bound. -/
theorem denseLagrangeNodeCosted_cost_le (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (points evals : List Fp) (index : Fin (2 ^ k)) :
    (denseLagrangeNodeCosted costs read omegaAccess k points evals index).2 ≤
      denseLagrangeNodeCostBudget costs read omegaAccess k points.length evals.length := by
  have hp := fieldPowerCosted_cost costs.multiply (omegaOf k) index.val
  have hi := Nat.mul_le_mul_right (costs.multiply + 1) (Nat.le_of_lt index.isLt)
  have hv := lagrangeEvalCosted_cost_le costs read
    ((fieldPowerCosted costs.multiply (omegaOf k) index.val).1, 1) points evals
  change (lagrangeEvalCosted costs read
    ((fieldPowerCosted costs.multiply (omegaOf k) index.val).1, 1) points evals).2 ≤
    lagrangeEvalCostBudget costs read points.length evals.length 1 at hv
  change omegaAccess + _ + _ + 2 ≤ _
  unfold denseLagrangeNodeCostBudget
  omega

/-- Construct all interpolant coefficients by a fully counted inverse DFT of its actual indexed evaluator. -/
@[irreducible] def denseLagrangeCoefficientsCosted (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (points evals : List Fp) : List Fp × ℕ :=
  rowCoefficientsCosted costs (omegaOf k, omegaAccess)
    (denseLagrangeNodeCosted costs read omegaAccess k points evals)

/-- A large enough internal domain recovers the exact original interpolant for every point/value list. -/
theorem denseLagrangeCoefficientsCosted_result (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (hk : k ≤ 32) (points evals : List Fp) (hpoints : points.length ≤ 2 ^ k) :
    densePolynomial (denseLagrangeCoefficientsCosted costs read omegaAccess k points evals).1 =
      lagrangePoly points evals := by
  have hd := lagrangePoly_natDegree_le_total points evals
  have hn : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdegree : (lagrangePoly points evals).natDegree < 2 ^ k := by omega
  unfold denseLagrangeCoefficientsCosted
  rewrite [densePolynomial_rowCoefficientsCosted costs k hk omegaAccess]
  simp only [denseLagrangeNodeCosted_result]
  exact rowPolynomial_evaluations k hk (lagrangePoly points evals) hdegree

/-- The materialized interpolant retains the entire chosen coefficient capacity. -/
theorem denseLagrangeCoefficientsCosted_length (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (points evals : List Fp) :
    (denseLagrangeCoefficientsCosted costs read omegaAccess k points evals).1.length = 2 ^ k := by
  unfold denseLagrangeCoefficientsCosted
  exact ofFnCosted_length (rowCoefficientCosted costs (omegaOf k, omegaAccess)
    (denseLagrangeNodeCosted costs read omegaAccess k points evals))

/-- Complete interpolant budget derived from the actual point/value storage dimensions. -/
def denseLagrangeCoefficientsCostBudget (costs : FieldOperationCosts) (read omegaAccess k points evals : ℕ) : ℕ :=
  2 ^ k * (rowCoefficientCostBudget costs (2 ^ k)
    (denseLagrangeNodeCostBudget costs read omegaAccess k points evals) omegaAccess + 1) +
    2 ^ k * 2 ^ k + 1

/-- Every point construction, interpolation evaluation, coefficient operation, and stored output is counted. -/
theorem denseLagrangeCoefficientsCosted_cost_le (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (points evals : List Fp) :
    (denseLagrangeCoefficientsCosted costs read omegaAccess k points evals).2 ≤
      denseLagrangeCoefficientsCostBudget costs read omegaAccess k points.length evals.length := by
  unfold denseLagrangeCoefficientsCosted
  exact rowCoefficientsCosted_cost_le costs (omegaOf k, omegaAccess)
    (denseLagrangeNodeCosted costs read omegaAccess k points evals)
    (denseLagrangeNodeCostBudget costs read omegaAccess k points.length evals.length)
    (denseLagrangeNodeCosted_cost_le costs read omegaAccess k points evals)

end Zcash.Snark.ZeroKnowledge
