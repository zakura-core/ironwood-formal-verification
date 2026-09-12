import Zcash.Snark.ZeroKnowledge.DenseRowPolynomial

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark CompPoly

/-- Materialize every private row polynomial, retaining every row-reader and inverse-DFT cost. -/
def privatePolynomialCoefficientsCosted (costs : FieldOperationCosts) {n : ℕ} (omega : Fp × ℕ)
    (rows : List (Fin n → Fp × ℕ)) : List (List Fp) × ℕ :=
  mapListCosted (rowCoefficientsCosted costs omega) rows

/-- Every stored private polynomial is the original row interpolant, in the same order. -/
theorem privatePolynomialCoefficientsCosted_result (costs : FieldOperationCosts) (k : ℕ) (hk : k ≤ 32)
    (omegaAccess : ℕ) (rows : List (Fin (2 ^ k) → Fp × ℕ)) :
    ((privatePolynomialCoefficientsCosted costs (omegaOf k, omegaAccess) rows).1.map densePolynomial) =
      (rows.map (fun column => rowPolynomial (omegaOf k) (fun index => (column index).1))) := by
  simp only [privatePolynomialCoefficientsCosted, mapListCosted_result, List.map_map, Function.comp_def,
    densePolynomial_rowCoefficientsCosted costs k hk omegaAccess]

/-- There is one stored polynomial per private column. -/
theorem privatePolynomialCoefficientsCosted_length (costs : FieldOperationCosts) {n : ℕ} (omega : Fp × ℕ)
    (rows : List (Fin n → Fp × ℕ)) :
    (privatePolynomialCoefficientsCosted costs omega rows).1.length = rows.length := by
  rw [privatePolynomialCoefficientsCosted, mapListCosted_result, List.length_map]

/-- Every private polynomial is materialized at its complete commitment width. -/
theorem privatePolynomialCoefficientsCosted_width (costs : FieldOperationCosts) {n : ℕ} (omega : Fp × ℕ)
    (rows : List (Fin n → Fp × ℕ)) (poly : List Fp)
    (hpoly : poly ∈ (privatePolynomialCoefficientsCosted costs omega rows).1) : poly.length = n := by
  simp only [privatePolynomialCoefficientsCosted, mapListCosted_result, List.mem_map] at hpoly
  obtain ⟨column, _, rfl⟩ := hpoly
  exact ofFnCosted_length (rowCoefficientCosted costs omega column)

/-- The complete private-polynomial budget includes all field work and both levels of output storage. -/
theorem privatePolynomialCoefficientsCosted_cost_le (costs : FieldOperationCosts) {n : ℕ} (omega : Fp × ℕ)
    (rows : List (Fin n → Fp × ℕ)) (rowRead : ℕ)
    (hrows : ∀ column ∈ rows, ∀ index, (column index).2 ≤ rowRead) :
    (privatePolynomialCoefficientsCosted costs omega rows).2 ≤
      rows.length * (n * (rowCoefficientCostBudget costs n rowRead omega.2 + 1) + n * n + 2) + 1 := by
  exact mapListCosted_cost_le (rowCoefficientsCosted costs omega) rows
    (n * (rowCoefficientCostBudget costs n rowRead omega.2 + 1) + n * n + 1)
    (fun column hcolumn => rowCoefficientsCosted_cost_le costs omega column rowRead (hrows column hcolumn))

/-- Defaulted reads commute with polynomial decoding, including a missing private column. -/
theorem densePolynomial_getD (polys : List (List Fp)) (index : ℕ) :
    densePolynomial (polys.getD index []) = (polys.map densePolynomial).getD index 0 := by
  induction polys generalizing index with
  | nil => simp only [List.getD_nil, densePolynomial, List.map_nil]
  | cons first rest ih => cases index <;> simp only [List.map_cons, List.getD_cons_zero, List.getD_cons_succ, ih]

end Zcash.Snark.ZeroKnowledge
