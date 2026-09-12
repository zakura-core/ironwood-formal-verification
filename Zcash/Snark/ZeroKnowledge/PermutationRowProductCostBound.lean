import Zcash.Snark.ZeroKnowledge.PermutationRowProductCost

namespace Zcash.Snark.ZeroKnowledge
variable {F : Type*} [Field F]

/-- Complete identity-product budget, polynomial in pair count and the actual power exponents. -/
def permutationRowNumeratorCostBudget (costs : FieldOperationCosts)
    (read pairsCost count betaRead gammaRead omegaRead deltaRead chunkLen chunk row : ℕ) : ℕ :=
  pairsCost + count * (2 * count + read + betaRead + gammaRead + omegaRead + 2 * deltaRead +
    (row + chunk * chunkLen + count) * (costs.multiply + 1) +
    4 * costs.multiply + 2 * costs.add + 15) + count * count + 4

/-- Complete sigma-product budget, retaining pair preparation and both coordinate reads. -/
def permutationRowDenominatorCostBudget (costs : FieldOperationCosts)
    (read pairsCost count betaRead gammaRead : ℕ) : ℕ :=
  pairsCost + count * (4 * count + 2 * read + betaRead + gammaRead +
    2 * costs.multiply + 2 * costs.add + 9) + count * count + 4

/-- Every loop and provider cost is retained in the original numerator product's bound. -/
theorem permutationRowNumeratorCosted_cost_le (costs : FieldOperationCosts) (read : ℕ)
    (pairs : ℕ → ℕ → List (F × F) × ℕ) (beta gamma omega delta : F × ℕ)
    (chunkLen chunk row : ℕ) :
    (permutationRowNumeratorCosted costs read pairs beta gamma omega delta chunkLen chunk row).2 ≤
      permutationRowNumeratorCostBudget costs read (pairs chunk row).2 (pairs chunk row).1.length
        beta.2 gamma.2 omega.2 delta.2 chunkLen chunk row := by
  let values := pairs chunk row
  let n := values.1.length
  let access := 2 * n + read + beta.2 + gamma.2 + omega.2 + 2 * delta.2 +
    (row + chunk * chunkLen + n) * (costs.multiply + 1) + 3 * costs.multiply + 2 * costs.add + 13
  have hf (index : Fin (lengthListCosted values.1).1) : (permutationNumeratorFactorCosted costs
      (getDListCosted read (0, 0) values.1 index.val) beta gamma omega delta chunkLen chunk row index.val).2 ≤
      access := by
    rw [permutationNumeratorFactorCosted_cost]
    have hp := getDListCosted_cost_le read ((0 : F), 0) values.1 index.val
    have hindex : index.val < n := by simpa only [lengthListCosted_result, n] using index.isLt
    have hi := Nat.mul_le_mul_right (costs.multiply + 1) (Nat.le_of_lt hindex)
    dsimp only [access, n]
    dsimp only [n] at hi
    nlinarith
  have h := prodFinCosted_cost_le costs.multiply
    (fun index : Fin (lengthListCosted values.1).1 => permutationNumeratorFactorCosted costs
      (getDListCosted read (0, 0) values.1 index.val) beta gamma omega delta chunkLen chunk row index.val)
    access hf
  simp only [lengthListCosted_result] at h
  simp only [permutationRowNumeratorCosted, lengthListCosted_cost]
  change values.2 + (n + 1) + (prodFinCosted costs.multiply
    (fun index : Fin (lengthListCosted values.1).1 => permutationNumeratorFactorCosted costs
      (getDListCosted read (0, 0) values.1 index.val) beta gamma omega delta chunkLen chunk row index.val)).2 + 2 ≤ _
  dsimp only [permutationRowNumeratorCostBudget]
  dsimp only [access, n, values] at h ⊢
  nlinarith

/-- Every loop and provider cost is retained in the original denominator product's bound. -/
theorem permutationRowDenominatorCosted_cost_le (costs : FieldOperationCosts) (read : ℕ)
    (pairs : ℕ → ℕ → List (F × F) × ℕ) (beta gamma : F × ℕ) (chunk row : ℕ) :
    (permutationRowDenominatorCosted costs read pairs beta gamma chunk row).2 ≤
      permutationRowDenominatorCostBudget costs read (pairs chunk row).2 (pairs chunk row).1.length
        beta.2 gamma.2 := by
  let values := pairs chunk row
  let n := values.1.length
  let access := 4 * n + 2 * read + beta.2 + gamma.2 + costs.multiply + 2 * costs.add + 7
  have hf (index : Fin (lengthListCosted values.1).1) : (permutationDenominatorFactorCosted costs
      (getDListCosted read (0, 0) values.1 index.val) beta gamma).2 ≤ access := by
    rw [permutationDenominatorFactorCosted_cost]
    have hp := getDListCosted_cost_le read ((0 : F), 0) values.1 index.val
    dsimp only [access, n]
    omega
  have h := prodFinCosted_cost_le costs.multiply
    (fun index : Fin (lengthListCosted values.1).1 => permutationDenominatorFactorCosted costs
      (getDListCosted read (0, 0) values.1 index.val) beta gamma) access hf
  simp only [lengthListCosted_result] at h
  simp only [permutationRowDenominatorCosted, lengthListCosted_cost]
  change values.2 + (n + 1) + (prodFinCosted costs.multiply
    (fun index : Fin (lengthListCosted values.1).1 => permutationDenominatorFactorCosted costs
      (getDListCosted read (0, 0) values.1 index.val) beta gamma)).2 + 2 ≤ _
  dsimp only [permutationRowDenominatorCostBudget]
  dsimp only [access, n, values] at h ⊢
  nlinarith

end Zcash.Snark.ZeroKnowledge
