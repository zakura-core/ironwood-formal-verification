import Zcash.Snark.ZeroKnowledge.PublicFoldCost
import Zcash.Snark.ZeroKnowledge.IpaScalarCost
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

namespace Zcash.Snark.ZeroKnowledge
variable {F : Type*} [Field F]

/-- One original sparse-mask summand, including its support and root-enforcing constant term. -/
def sparseIpaTermCosted (costs : FieldOperationCosts) (equal : ℕ) {k : ℕ}
    (point : F × ℕ) (alphas : Fin k → F × ℕ) (term : Fin k) (index : Fin (2 ^ k)) : F × ℕ :=
  let support := powTwoCosted term.val
  let power := squarePowerCosted costs.multiply point.1 term.val
  let alpha := alphas term
  (alpha.1 * ((if index.val = support.1 then 1 else 0) - (if index.val = 0 then power.1 else 0)),
    support.2 + power.2 + alpha.2 + point.2 + 2 * equal + costs.add + costs.negate + costs.multiply + 5)

/-- Erasure recovers the exact original sparse basis coefficient. -/
theorem sparseIpaTermCosted_result (costs : FieldOperationCosts) (equal : ℕ) {k : ℕ}
    (point : F × ℕ) (alphas : Fin k → F × ℕ) (term : Fin k) (index : Fin (2 ^ k)) :
    (sparseIpaTermCosted costs equal point alphas term index).1 =
      ((alphas term).1 • (Pi.single (powerIndex term) (1 : F) -
        point.1 ^ (2 ^ term.val) • Pi.single (0 : Fin (2 ^ k)) (1 : F)) : Fin (2 ^ k) → F) index := by
  have hpositive : 0 < (2 : ℕ) ^ term.val := by positivity
  have hsmall : (2 : ℕ) ^ term.val < 2 ^ k := (powerIndex term).isLt
  simp only [sparseIpaTermCosted, powTwoCosted_result, squarePowerCosted_result,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply, powerIndex, Fin.ext_iff]
  split_ifs <;> simp_all [Nat.mod_eq_of_lt hsmall]

/-- Count a complete sparse-mask coefficient by summing all original support contributions. -/
def sparseIpaCoefficientCosted (costs : FieldOperationCosts) (equal : ℕ) {k : ℕ}
    (point : F × ℕ) (alphas : Fin k → F × ℕ) (index : Fin (2 ^ k)) : F × ℕ :=
  sumFinCosted costs.add fun term => sparseIpaTermCosted costs equal point alphas term index

/-- Every counted coefficient is exactly the Common-225 mask used by the reference prover. -/
theorem sparseIpaCoefficientCosted_result (costs : FieldOperationCosts) (equal : ℕ) {k : ℕ}
    (point : F × ℕ) (alphas : Fin k → F × ℕ) (index : Fin (2 ^ k)) :
    (sparseIpaCoefficientCosted costs equal point alphas index).1 =
      sparseIpaCoefficients point.1 (fun i => (alphas i).1) index := by
  simp only [sparseIpaCoefficientCosted, sumFinCosted_result, sparseIpaTermCosted_result,
    sparseIpaCoefficients, Finset.sum_apply]

/-- Explicit sparse-coefficient access budget, including all support powers and mask reads. -/
def sparseIpaCoefficientCostBudget (costs : FieldOperationCosts)
    (equal k pointRead alphaRead : ℕ) : ℕ :=
  k * (2 * k + 1 + (k * (costs.multiply + 1) + 1) + alphaRead + pointRead +
    2 * equal + costs.add + costs.negate + costs.multiply + 5 + costs.add + 1) + k * k + 1

/-- Bound the complete original sparse-mask coefficient computation. -/
theorem sparseIpaCoefficientCosted_cost_le (costs : FieldOperationCosts) (equal : ℕ) {k : ℕ}
    (point : F × ℕ) (alphas : Fin k → F × ℕ) (alphaRead : ℕ)
    (halphas : ∀ i, (alphas i).2 ≤ alphaRead) (index : Fin (2 ^ k)) :
    (sparseIpaCoefficientCosted costs equal point alphas index).2 ≤
      sparseIpaCoefficientCostBudget costs equal k point.2 alphaRead := by
  unfold sparseIpaCoefficientCosted sparseIpaCoefficientCostBudget
  apply sumFinCosted_cost_le
  intro term
  have ha := halphas term
  have hi := Nat.le_of_lt term.isLt
  have hp := Nat.mul_le_mul_right (costs.multiply + 1) hi
  simp only [sparseIpaTermCosted, powTwoCosted_cost, squarePowerCosted_cost]
  omega

end Zcash.Snark.ZeroKnowledge
