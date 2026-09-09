import Zcash.Snark.ZeroKnowledge.CosetPolynomial
import Zcash.Snark.ZeroKnowledge.DensePolynomialRotate
import Zcash.Snark.ZeroKnowledge.StoredRowsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark CompPoly

/-- Materialize all coset values once, interpolate their stored vector, and undo the variable shift. -/
def cosetCoefficientsCosted (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (factor : Fp × ℕ) (values : Fin (2 ^ k) → Fp × ℕ) : List Fp × ℕ :=
  let samples := ofFnCosted values
  let coefficients := rowCoefficientsCosted costs (omegaOf k, omegaAccess)
    (fun index : Fin (2 ^ k) => getDListCosted read 0 samples.1 index.val)
  let rotated := denseRotateCosted read costs.multiply
    (factor.1⁻¹, factor.2 + costs.inverse + 1) coefficients.1
  (rotated.1, samples.2 + coefficients.2 + rotated.2 + 1)

/-- Every below-capacity polynomial is reconstructed exactly from its fully priced coset values. -/
theorem cosetCoefficientsCosted_result (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (hk : k ≤ 32) (factor : Fp × ℕ) (values : Fin (2 ^ k) → Fp × ℕ) (poly : CPoly)
    (hfactor : factor.1 ≠ 0) (hdegree : poly.natDegree < 2 ^ k)
    (hvalues : ∀ index, (values index).1 = poly.eval (factor.1 * omegaOf k ^ index.val)) :
    densePolynomial (cosetCoefficientsCosted costs read omegaAccess k factor values).1 = poly := by
  rw [cosetCoefficientsCosted, denseRotateCosted_result,
    densePolynomial_rowCoefficientsCosted costs k hk omegaAccess]
  simp only [ofFnCosted_result, getDListCosted_ofFn_result, hvalues]
  exact rowPolynomial_coset_evaluations k hk poly factor.1 hfactor hdegree

/-- Interpolation materializes the full declared coefficient width on every input. -/
theorem cosetCoefficientsCosted_length (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (factor : Fp × ℕ) (values : Fin (2 ^ k) → Fp × ℕ) :
    (cosetCoefficientsCosted costs read omegaAccess k factor values).1.length = 2 ^ k := by
  simp only [cosetCoefficientsCosted, denseRotateCosted_length, rowCoefficientsCosted, ofFnCosted_length]

/-- Full coset interpolation budget, retaining sample preparation, stored reads, inverse DFT, and rotation. -/
def cosetCoefficientsCostBudget (costs : FieldOperationCosts) (read omegaAccess k factorAccess valueAccess : ℕ) : ℕ :=
  let n := 2 ^ k
  (n * (valueAccess + 1) + n * n + 1) +
    (n * (rowCoefficientCostBudget costs n (2 * n + read + 1) omegaAccess + 1) + n * n + 1) +
    (factorAccess + costs.inverse + 1 + n * (3 * read + 2 * costs.multiply + 4) + 2) + 1

/-- The complete algorithm fits the explicit polynomial budget for all supplied values. -/
theorem cosetCoefficientsCosted_cost_le (costs : FieldOperationCosts) (read omegaAccess k : ℕ)
    (factor : Fp × ℕ) (values : Fin (2 ^ k) → Fp × ℕ)
    (valueAccess : ℕ) (hvalues : ∀ index, (values index).2 ≤ valueAccess) :
    (cosetCoefficientsCosted costs read omegaAccess k factor values).2 ≤
      cosetCoefficientsCostBudget costs read omegaAccess k factor.2 valueAccess := by
  let samples := ofFnCosted values
  let coefficients := rowCoefficientsCosted costs (omegaOf k, omegaAccess)
    (fun index : Fin (2 ^ k) => getDListCosted read (0 : Fp) samples.1 index.val)
  have hs := ofFnCosted_cost_le values valueAccess hvalues
  have hc := rowCoefficientsCosted_cost_le costs (omegaOf k, omegaAccess)
    (fun index : Fin (2 ^ k) => getDListCosted read (0 : Fp) samples.1 index.val)
    (2 * (2 ^ k) + read + 1) (by
      intro index
      simpa only [samples, ofFnCosted_length] using getDListCosted_cost_le read (0 : Fp) samples.1 index.val)
  have hr := denseRotateCosted_cost read costs.multiply
    (factor.1⁻¹, factor.2 + costs.inverse + 1) coefficients.1
  have hl : coefficients.1.length = 2 ^ k := ofFnCosted_length _
  rw [hl] at hr
  change samples.2 ≤ _ at hs
  change coefficients.2 ≤ (2 ^ k) *
    (rowCoefficientCostBudget costs (2 ^ k) (2 * (2 ^ k) + read + 1) omegaAccess + 1) +
    (2 ^ k) * (2 ^ k) + 1 at hc
  change samples.2 + coefficients.2 + _ + 1 ≤ _
  rw [hr]
  dsimp only [cosetCoefficientsCostBudget]
  omega

end Zcash.Snark.ZeroKnowledge
