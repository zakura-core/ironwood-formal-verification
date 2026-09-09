import Zcash.Snark.ZeroKnowledge.PermutationFactorCost
import Zcash.Snark.ZeroKnowledge.PermutationRowConstraints
import Zcash.Snark.ZeroKnowledge.ListTraversalCost
import Zcash.Snark.ZeroKnowledge.ListIndexCost

namespace Zcash.Snark.ZeroKnowledge
variable {F : Type*} [Field F]

/-- Compute a row's complete identity-named product after materializing its factor pairs. -/
def permutationRowNumeratorCosted (costs : FieldOperationCosts) (read : ℕ)
    (pairs : ℕ → ℕ → List (F × F) × ℕ) (beta gamma omega delta : F × ℕ)
    (chunkLen chunk row : ℕ) : F × ℕ :=
  let values := pairs chunk row
  let count := lengthListCosted values.1
  let product := prodFinCosted costs.multiply fun index : Fin count.1 =>
    permutationNumeratorFactorCosted costs (getDListCosted read (0, 0) values.1 index.val)
      beta gamma omega delta chunkLen chunk row index.val
  (product.1, values.2 + count.2 + product.2 + 2)

/-- Compute the complete sigma-named product with the same materialized-pair and indexing costs. -/
def permutationRowDenominatorCosted (costs : FieldOperationCosts) (read : ℕ)
    (pairs : ℕ → ℕ → List (F × F) × ℕ) (beta gamma : F × ℕ) (chunk row : ℕ) : F × ℕ :=
  let values := pairs chunk row
  let count := lengthListCosted values.1
  let product := prodFinCosted costs.multiply fun index : Fin count.1 =>
    permutationDenominatorFactorCosted costs (getDListCosted read (0, 0) values.1 index.val) beta gamma
  (product.1, values.2 + count.2 + product.2 + 2)

/-- The counted numerator has exactly the original packed-pair product and column-name stride. -/
theorem permutationRowNumeratorCosted_result (costs : FieldOperationCosts) (read : ℕ)
    (pairs : ℕ → ℕ → List (F × F) × ℕ) (beta gamma omega delta : F × ℕ)
    (chunkLen chunk row : ℕ) :
    (permutationRowNumeratorCosted costs read pairs beta gamma omega delta chunkLen chunk row).1 =
      permutationRowNumerator (fun c r => (pairs c r).1) beta.1 gamma.1 omega.1 delta.1 chunkLen chunk row := by
  simp only [permutationRowNumeratorCosted, prodFinCosted_result,
    permutationNumeratorFactorCosted_result, getDListCosted_result, permutationRowNumerator]
  simpa only [lengthListCosted_result] using Fin.prod_univ_eq_prod_range (fun index : ℕ =>
    ((pairs chunk row).1.getD index (0, 0)).1 +
      beta.1 * omega.1 ^ row * delta.1 ^ (chunk * chunkLen) * delta.1 ^ index + gamma.1)
    (lengthListCosted (pairs chunk row).1).1

/-- The counted denominator has exactly the original sigma-factor product. -/
theorem permutationRowDenominatorCosted_result (costs : FieldOperationCosts) (read : ℕ)
    (pairs : ℕ → ℕ → List (F × F) × ℕ) (beta gamma : F × ℕ) (chunk row : ℕ) :
    (permutationRowDenominatorCosted costs read pairs beta gamma chunk row).1 =
      permutationRowDenominator (fun c r => (pairs c r).1) beta.1 gamma.1 chunk row := by
  simp only [permutationRowDenominatorCosted, prodFinCosted_result,
    permutationDenominatorFactorCosted_result, getDListCosted_result, permutationRowDenominator]
  simpa only [lengthListCosted_result] using Fin.prod_univ_eq_prod_range (fun index : ℕ =>
    ((pairs chunk row).1.getD index (0, 0)).1 + beta.1 * ((pairs chunk row).1.getD index (0, 0)).2 + gamma.1)
    (lengthListCosted (pairs chunk row).1).1

end Zcash.Snark.ZeroKnowledge
