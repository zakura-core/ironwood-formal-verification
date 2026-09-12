import Zcash.Snark.ZeroKnowledge.RowCoefficientCost
import Zcash.Snark.ZeroKnowledge.PolynomialCommitment

/-!
# Public row evaluation and commitments with preparation costs

These algorithms build the needed coefficients from the original rows, using
the counted inverse-DFT formula. Their results agree with canonical row-polynomial
evaluation and commitment. The bounds retain all row and generator providers;
they do not assume a supplied polynomial has already been interpolated.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Materialize every coefficient, charging the complete construction at each index. -/
def rowCoefficientsCosted (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) : List Fp × ℕ :=
  ofFnCosted (rowCoefficientCosted costs omega values)

/-- The constructed list is exactly the canonical polynomial's full coefficient vector. -/
theorem rowCoefficientsCosted_result (costs : FieldOperationCosts) (k : ℕ) (hk : k ≤ 32)
    (omegaAccess : ℕ) (values : Fin (2 ^ k) → Fp × ℕ) :
    (rowCoefficientsCosted costs (omegaOf k, omegaAccess) values).1 =
      List.ofFn (polynomialCoefficients (2 ^ k)
        (rowPolynomial (omegaOf k) (fun row => (values row).1))) := by
  rw [rowCoefficientsCosted, ofFnCosted_result]
  congr 1
  funext index
  exact rowCoefficientCosted_rowPolynomial costs k hk omegaAccess values index

/-- Coefficient materialization includes every row scan and every output list cell. -/
theorem rowCoefficientsCosted_cost_le (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ)
    (rowRead : ℕ) (hread : ∀ row, (values row).2 ≤ rowRead) :
    (rowCoefficientsCosted costs omega values).2 ≤
      n * (rowCoefficientCostBudget costs n rowRead omega.2 + 1) + n * n + 1 :=
  ofFnCosted_cost_le _ _ (fun index =>
    rowCoefficientCosted_cost_le costs omega values index rowRead hread)

/-- Evaluate directly from freshly constructed coefficients, including the point-power loops. -/
def rowPolynomialEvalCosted (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) (point : Fp × ℕ) : Fp × ℕ :=
  sumFinCosted costs.add fun index : Fin n =>
    let coefficient := rowCoefficientCosted costs omega values index
    let power := fieldPowerCosted costs.multiply point.1 index.val
    (coefficient.1 * power.1, coefficient.2 + point.2 + power.2 + costs.multiply + 1)

/-- Every evaluation challenge gives exactly the original canonical polynomial value. -/
theorem rowPolynomialEvalCosted_result (costs : FieldOperationCosts) (k : ℕ) (hk : k ≤ 32)
    (omegaAccess : ℕ) (values : Fin (2 ^ k) → Fp × ℕ) (point : Fp × ℕ) :
    (rowPolynomialEvalCosted costs (omegaOf k, omegaAccess) values point).1 =
      (rowPolynomial (omegaOf k) (fun row => (values row).1)).eval point.1 := by
  rw [← coefficientEvaluation_polynomialCoefficients _ point.1
    (rowPolynomial_natDegree_lt (omegaOf_powers_injective k hk) (Nat.two_pow_pos k))]
  simp only [rowPolynomialEvalCosted, sumFinCosted_result, fieldPowerCosted_result,
    coefficientEvaluation]
  apply Finset.sum_congr rfl
  intro index _
  rw [rowCoefficientCosted_rowPolynomial costs k hk omegaAccess values index]
  rfl

/-- The full evaluation budget includes interpolation, point access, and exponentiation. -/
theorem rowPolynomialEvalCosted_cost_le (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) (point : Fp × ℕ)
    (rowRead : ℕ) (hread : ∀ row, (values row).2 ≤ rowRead) :
    (rowPolynomialEvalCosted costs omega values point).2 ≤
      n * (rowCoefficientCostBudget costs n rowRead omega.2 + point.2 +
        n * (costs.multiply + 1) + costs.multiply + costs.add + 3) + n * n + 1 := by
  let budget := rowCoefficientCostBudget costs n rowRead omega.2 + point.2 +
    n * (costs.multiply + 1) + costs.multiply + 2
  have hentry (index : Fin n) :
      (rowCoefficientCosted costs omega values index).2 + point.2 +
        (fieldPowerCosted costs.multiply point.1 index.val).2 + costs.multiply + 1 ≤ budget := by
    have hc := rowCoefficientCosted_cost_le costs omega values index rowRead hread
    have hp := Nat.mul_le_mul_right (costs.multiply + 1) (Nat.le_of_lt index.isLt)
    rw [fieldPowerCosted_cost]
    dsimp only [budget]
    omega
  have hsum := sumFinCosted_cost_le costs.add (fun index : Fin n =>
      ((rowCoefficientCosted costs omega values index).1 *
        (fieldPowerCosted costs.multiply point.1 index.val).1,
       (rowCoefficientCosted costs omega values index).2 + point.2 +
        (fieldPowerCosted costs.multiply point.1 index.val).2 + costs.multiply + 1)) budget hentry
  calc
    _ ≤ n * (budget + costs.add + 1) + n * n + 1 := hsum
    _ = _ := by dsimp only [budget]; ring

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Commit to original public rows, paying for coefficient preparation and the blinding term. -/
def rowPolynomialCommitmentCosted (costs : FieldOperationCosts) (groupAdd groupScale : ℕ) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) (generators : Fin n → G × ℕ)
    (W : G × ℕ) (blind : Fp × ℕ) : G × ℕ :=
  let commitment := sumFinCosted groupAdd fun index : Fin n =>
    let coefficient := rowCoefficientCosted costs omega values index
    let generator := generators index
    (coefficient.1 • generator.1, coefficient.2 + generator.2 + groupScale + 1)
  (commitment.1 + blind.1 • W.1,
    commitment.2 + blind.2 + W.2 + groupScale + groupAdd + 1)

/-- Cost erasure is the reference commitment to the canonical public row polynomial. -/
theorem rowPolynomialCommitmentCosted_result (costs : FieldOperationCosts)
    (groupAdd groupScale k : ℕ) (hk : k ≤ 32) (omegaAccess : ℕ)
    (values : Fin (2 ^ k) → Fp × ℕ) (generators : Fin (2 ^ k) → G × ℕ)
    (W : G × ℕ) (blind : Fp × ℕ) :
    (rowPolynomialCommitmentCosted costs groupAdd groupScale (omegaOf k, omegaAccess)
      values generators W blind).1 =
      polynomialCommitment (fun index => (generators index).1) W.1
        (rowPolynomial (omegaOf k) (fun row => (values row).1)) blind.1 := by
  simp only [rowPolynomialCommitmentCosted, sumFinCosted_result, polynomialCommitment, commitGen]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  rw [rowCoefficientCosted_rowPolynomial costs k hk omegaAccess values index]
  rfl

/-- The commitment bound charges all row preparation and generator reads in the same computation. -/
theorem rowPolynomialCommitmentCosted_cost_le (costs : FieldOperationCosts)
    (groupAdd groupScale : ℕ) {n : ℕ} (omega : Fp × ℕ) (values : Fin n → Fp × ℕ)
    (generators : Fin n → G × ℕ) (W : G × ℕ) (blind : Fp × ℕ)
    (rowRead generatorRead : ℕ) (hread : ∀ row, (values row).2 ≤ rowRead)
    (hgenerator : ∀ index, (generators index).2 ≤ generatorRead) :
    (rowPolynomialCommitmentCosted costs groupAdd groupScale omega values generators W blind).2 ≤
      n * (rowCoefficientCostBudget costs n rowRead omega.2 + generatorRead + groupScale + groupAdd + 2) +
        n * n + blind.2 + W.2 + groupScale + groupAdd + 2 := by
  let budget := rowCoefficientCostBudget costs n rowRead omega.2 + generatorRead + groupScale + 1
  have hentry (index : Fin n) :
      (rowCoefficientCosted costs omega values index).2 + (generators index).2 + groupScale + 1 ≤ budget := by
    have hc := rowCoefficientCosted_cost_le costs omega values index rowRead hread
    have hg := hgenerator index
    dsimp only [budget]
    omega
  have hsum := sumFinCosted_cost_le groupAdd (fun index : Fin n =>
      ((rowCoefficientCosted costs omega values index).1 • (generators index).1,
        (rowCoefficientCosted costs omega values index).2 + (generators index).2 + groupScale + 1)) budget hentry
  simp only [rowPolynomialCommitmentCosted]
  calc
    _ ≤ (n * (budget + groupAdd + 1) + n * n + 1) + blind.2 + W.2 + groupScale + groupAdd + 1 := by omega
    _ = _ := by dsimp only [budget]; ring

end Zcash.Snark.ZeroKnowledge
