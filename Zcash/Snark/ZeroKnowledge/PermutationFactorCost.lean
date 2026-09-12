import Zcash.Snark.ZeroKnowledge.FiniteProductCost
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost

namespace Zcash.Snark.ZeroKnowledge
variable {F : Type*} [Field F]

/-- One original identity-named permutation factor, with all power and operand costs. -/
def permutationNumeratorFactorCosted (costs : FieldOperationCosts)
    (pair : (F × F) × ℕ) (beta gamma omega delta : F × ℕ)
    (chunkLen chunk row index : ℕ) : F × ℕ :=
  let rowPower := fieldPowerCosted costs.multiply omega.1 row
  let chunkPower := fieldPowerCosted costs.multiply delta.1 (chunk * chunkLen)
  let indexPower := fieldPowerCosted costs.multiply delta.1 index
  let named := fieldMultiplyCosted costs
    (fieldMultiplyCosted costs
      (fieldMultiplyCosted costs beta (rowPower.1, omega.2 + rowPower.2 + 1))
      (chunkPower.1, delta.2 + chunkPower.2 + 1))
    (indexPower.1, delta.2 + indexPower.2 + 1)
  fieldAddCosted costs (fieldAddCosted costs (pair.1.1, pair.2 + 1) named) gamma

/-- Erasure gives the verifier's exact identity name and chunk stride. -/
theorem permutationNumeratorFactorCosted_result (costs : FieldOperationCosts)
    (pair : (F × F) × ℕ) (beta gamma omega delta : F × ℕ)
    (chunkLen chunk row index : ℕ) :
    (permutationNumeratorFactorCosted costs pair beta gamma omega delta chunkLen chunk row index).1 =
      pair.1.1 + beta.1 * omega.1 ^ row * delta.1 ^ (chunk * chunkLen) * delta.1 ^ index + gamma.1 := by
  simp only [permutationNumeratorFactorCosted, fieldAddCosted_result,
    fieldMultiplyCosted_result, fieldPowerCosted_result]

/-- The identity-factor cost counts all three powers and every supplied operand. -/
theorem permutationNumeratorFactorCosted_cost (costs : FieldOperationCosts)
    (pair : (F × F) × ℕ) (beta gamma omega delta : F × ℕ)
    (chunkLen chunk row index : ℕ) :
    (permutationNumeratorFactorCosted costs pair beta gamma omega delta chunkLen chunk row index).2 =
      pair.2 + beta.2 + gamma.2 + omega.2 + 2 * delta.2 +
        (row + chunk * chunkLen + index) * (costs.multiply + 1) +
        3 * costs.multiply + 2 * costs.add + 12 := by
  simp only [permutationNumeratorFactorCosted, fieldAddCosted, fieldMultiplyCosted, fieldPowerCosted_cost]
  ring

/-- One original sigma-named factor, retaining both reads of the materialized pair. -/
def permutationDenominatorFactorCosted (costs : FieldOperationCosts)
    (pair : (F × F) × ℕ) (beta gamma : F × ℕ) : F × ℕ :=
  fieldAddCosted costs
    (fieldAddCosted costs (pair.1.1, pair.2 + 1)
      (fieldMultiplyCosted costs beta (pair.1.2, pair.2 + 1))) gamma

/-- Erasure preserves the original sigma factor. -/
theorem permutationDenominatorFactorCosted_result (costs : FieldOperationCosts)
    (pair : (F × F) × ℕ) (beta gamma : F × ℕ) :
    (permutationDenominatorFactorCosted costs pair beta gamma).1 =
      pair.1.1 + beta.1 * pair.1.2 + gamma.1 := by
  simp only [permutationDenominatorFactorCosted, fieldAddCosted_result, fieldMultiplyCosted_result]

/-- Exact sigma-factor cost, including every coordinate read and arithmetic operation. -/
theorem permutationDenominatorFactorCosted_cost (costs : FieldOperationCosts)
    (pair : (F × F) × ℕ) (beta gamma : F × ℕ) :
    (permutationDenominatorFactorCosted costs pair beta gamma).2 =
      2 * pair.2 + beta.2 + gamma.2 + costs.multiply + 2 * costs.add + 5 := by
  simp only [permutationDenominatorFactorCosted, fieldAddCosted, fieldMultiplyCosted]
  ring

end Zcash.Snark.ZeroKnowledge
