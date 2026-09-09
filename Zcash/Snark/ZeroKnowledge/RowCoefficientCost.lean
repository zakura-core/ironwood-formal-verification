import Zcash.Snark.ZeroKnowledge.FieldExponentCost
import Zcash.Snark.Keygen.Lagrange

/-!
# Counted construction of public row coefficients

The inverse-DFT formula computes each coefficient from the original row values.
All row reads, normalization, inverse powers, and summation work are counted;
there is no precomputed polynomial or unpriced interpolation callback.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- A single inverse-DFT summand with complete input and exponentiation costs. -/
def rowCoefficientSummandCosted (costs : FieldOperationCosts)
    (normalization inverseOmega value : Fp × ℕ) (row coefficient : ℕ) : Fp × ℕ :=
  let power := fieldPowerCosted costs.multiply inverseOmega.1 (row * coefficient)
  (value.1 * (normalization.1 * power.1),
    value.2 + normalization.2 + inverseOmega.2 + power.2 + 2 * costs.multiply + 2)

/-- The summand is the original row scaled by the closed Lagrange coefficient. -/
theorem rowCoefficientSummandCosted_result (costs : FieldOperationCosts)
    (normalization inverseOmega value : Fp × ℕ) (row coefficient : ℕ) :
    (rowCoefficientSummandCosted costs normalization inverseOmega value row coefficient).1 =
      value.1 * (normalization.1 * inverseOmega.1 ^ (row * coefficient)) := by
  simp only [rowCoefficientSummandCosted, fieldPowerCosted_result]

/-- The bounded indices give an explicit bound for the entire power loop. -/
theorem rowCoefficientSummandCosted_cost_le (costs : FieldOperationCosts)
    (normalization inverseOmega value : Fp × ℕ) {n : ℕ} (row coefficient : Fin n) :
    (rowCoefficientSummandCosted costs normalization inverseOmega value row.val coefficient.val).2 ≤
      value.2 + normalization.2 + inverseOmega.2 + n * n * (costs.multiply + 1) +
        2 * costs.multiply + 3 := by
  have hindices := Nat.mul_le_mul (Nat.le_of_lt row.isLt) (Nat.le_of_lt coefficient.isLt)
  have hpower := Nat.mul_le_mul_right (costs.multiply + 1) hindices
  simp only [rowCoefficientSummandCosted, fieldPowerCosted_cost]
  omega

/-- Construct one coefficient directly from the full supplied row vector. -/
def rowCoefficientCosted (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) (coefficient : Fin n) : Fp × ℕ :=
  let normalization := fieldInverseCosted costs (fieldNatCastCosted costs.add n)
  let inverseOmega := fieldInverseCosted costs omega
  sumFinCosted costs.add fun row =>
    rowCoefficientSummandCosted costs normalization inverseOmega (values row) row.val coefficient.val

/-- Erasure retains the exact inverse-DFT coefficient formula. -/
theorem rowCoefficientCosted_result (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) (coefficient : Fin n) :
    (rowCoefficientCosted costs omega values coefficient).1 =
      ∑ row : Fin n, (values row).1 * ((n : Fp)⁻¹ * omega.1⁻¹ ^ (row.val * coefficient.val)) := by
  simp only [rowCoefficientCosted, sumFinCosted_result, rowCoefficientSummandCosted_result,
    fieldInverseCosted_result, fieldNatCastCosted_result]

/-- Explicit coefficient budget, retaining the full row provider and domain-generator costs. -/
def rowCoefficientCostBudget (costs : FieldOperationCosts) (n rowRead omegaAccess : ℕ) : ℕ :=
  n * (rowRead + n * (costs.add + 1) + omegaAccess + 2 * costs.inverse +
    n * n * (costs.multiply + 1) + 2 * costs.multiply + costs.add + 7) + n * n + 1

/-- The complete coefficient construction has the stated polynomial structural bound. -/
theorem rowCoefficientCosted_cost_le (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) (coefficient : Fin n)
    (rowRead : ℕ) (hread : ∀ row, (values row).2 ≤ rowRead) :
    (rowCoefficientCosted costs omega values coefficient).2 ≤
      rowCoefficientCostBudget costs n rowRead omega.2 := by
  let normalization := fieldInverseCosted costs (fieldNatCastCosted (F := Fp) costs.add n)
  let inverseOmega := fieldInverseCosted costs omega
  let budget := rowRead + n * (costs.add + 1) + omega.2 + 2 * costs.inverse +
    n * n * (costs.multiply + 1) + 2 * costs.multiply + 6
  have hnormalization : normalization.2 = n * (costs.add + 1) + costs.inverse + 2 := by
    simp only [normalization, fieldInverseCosted, fieldNatCastCosted_cost]
    omega
  have hinverse : inverseOmega.2 = omega.2 + costs.inverse + 1 := rfl
  have hentry (row : Fin n) :
      (rowCoefficientSummandCosted costs normalization inverseOmega (values row)
        row.val coefficient.val).2 ≤ budget := by
    have h := rowCoefficientSummandCosted_cost_le costs normalization inverseOmega (values row)
      row coefficient
    have hr := hread row
    rw [hnormalization, hinverse] at h
    dsimp only [budget]
    omega
  have hsum := sumFinCosted_cost_le costs.add
    (fun row : Fin n => rowCoefficientSummandCosted costs normalization inverseOmega
      (values row) row.val coefficient.val) budget hentry
  calc
    _ ≤ n * (budget + costs.add + 1) + n * n + 1 := hsum
    _ = _ := by dsimp only [budget, rowCoefficientCostBudget]; ring

/-- On the specified domain, the counted value is the actual canonical polynomial coefficient. -/
theorem rowCoefficientCosted_rowPolynomial (costs : FieldOperationCosts) (k : ℕ) (hk : k ≤ 32)
    (omegaAccess : ℕ) (values : Fin (2 ^ k) → Fp × ℕ) (coefficient : Fin (2 ^ k)) :
    (rowCoefficientCosted costs (omegaOf k, omegaAccess) values coefficient).1 =
      polynomialCoefficients (2 ^ k) (rowPolynomial (omegaOf k) (fun row => (values row).1))
        coefficient := by
  rw [rowCoefficientCosted_result, polynomialCoefficients_rowPolynomial_eq_sum_single]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro row _
  rw [Keygen.polynomialCoefficients_single_closed k hk row coefficient]
  norm_cast

end Zcash.Snark.ZeroKnowledge
