import Zcash.Snark.ZeroKnowledge.StoredOpeningGroup
import Zcash.Snark.ZeroKnowledge.DensePolynomialEvaluation
import Zcash.Snark.ZeroKnowledge.MultiopenEvaluationCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Prepare every interpolation value and the actual query value of one stored opening group. -/
def storedOpeningSetCosted (costs : FieldOperationCosts) (read : ℕ) (point : Fp × ℕ)
    (group : StoredOpeningGroup) : (List Fp × List Fp × (Fp × ℕ)) × ℕ :=
  let nodes := densePolynomialNodeValuesCosted read costs.add costs.multiply group.coefficients group.points
  let value := listHornerCosted read costs.add costs.multiply point group.coefficients
  ((group.points, nodes.1, (value.1, read + 1)), nodes.2 + value.2 + 2 * read + 4)

/-- The prepared scalar data are precisely the original verifier-facing opening group. -/
theorem storedOpeningSetCosted_result (costs : FieldOperationCosts) (read : ℕ) (point : Fp × ℕ)
    (group : StoredOpeningGroup) :
    let entry := (storedOpeningSetCosted costs read point group).1
    (entry.1, entry.2.1, entry.2.2.1) = group.erase.toPolynomialOpeningGroup.forVerifier point.1 := by
  simp only [storedOpeningSetCosted, densePolynomialNodeValuesCosted_result,
    listHornerCosted_densePolynomial_result, StoredOpeningGroup.erase,
    PolynomialOpeningGroup.forVerifier, PolynomialOpeningGroup.values]

/-- The prepared data preserve the point count, including repeated points, and use stored claim reads. -/
theorem storedOpeningSetCosted_dimensions (costs : FieldOperationCosts) (read : ℕ) (point : Fp × ℕ)
    (group : StoredOpeningGroup) :
    let entry := (storedOpeningSetCosted costs read point group).1
    entry.1.length = group.points.length ∧ entry.2.1.length = group.points.length ∧ entry.2.2.2 = read + 1 := by
  simp only [storedOpeningSetCosted, densePolynomialNodeValuesCosted_length, and_self]

/-- Complete scalar-data preparation budget from the actual stored polynomial and point capacities. -/
def storedOpeningSetCostBudget (costs : FieldOperationCosts) (read pointRead width points : ℕ) : ℕ :=
  points * (width * (2 * read + costs.add + costs.multiply + 2) + 2) + 1 +
    (width * (pointRead + read + costs.add + costs.multiply + 1) + 1) + 2 * read + 4

/-- Every node and query evaluation, record access, and stored output enters the group preparation bound. -/
theorem storedOpeningSetCosted_cost_le (costs : FieldOperationCosts) (read : ℕ) (point : Fp × ℕ)
    (group : StoredOpeningGroup) :
    (storedOpeningSetCosted costs read point group).2 ≤
      storedOpeningSetCostBudget costs read point.2 group.coefficients.length group.points.length := by
  have hn := densePolynomialNodeValuesCosted_cost_le read costs.add costs.multiply group.coefficients group.points
  have hv := listHornerCosted_cost read costs.add costs.multiply point group.coefficients
  change (densePolynomialNodeValuesCosted read costs.add costs.multiply group.coefficients group.points).2 +
    (listHornerCosted read costs.add costs.multiply point group.coefficients).2 + 2 * read + 4 ≤ _
  unfold storedOpeningSetCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
