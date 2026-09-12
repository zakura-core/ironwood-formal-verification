import Zcash.Snark.ZeroKnowledge.PlonkOpeningRowsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)

attribute [local irreducible] rowCoefficientsCosted

/-- Counted row interpolation stores the full domain-sized coefficient vector. -/
theorem rowCoefficientsCosted_length (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) :
    (rowCoefficientsCosted costs omega values).1.length = n := by
  unfold rowCoefficientsCosted
  exact ofFnCosted_length (rowCoefficientCosted costs omega values)

/-- Full coefficient-vector preparation budget from the original row reader. -/
def rowPolynomialCoefficientsCostBudget (costs : FieldOperationCosts) (n rowRead omegaAccess : ℕ) : ℕ :=
  n * (rowCoefficientCostBudget costs n rowRead omegaAccess + 1) + n * n + 1

/-- Original row interpolation supplies every public coefficient provider's cost. -/
theorem rowPolynomialCoefficientsCosted_cost_le (costs : FieldOperationCosts) {n : ℕ}
    (omega : Fp × ℕ) (values : Fin n → Fp × ℕ) (rowRead : ℕ)
    (hvalues : ∀ row, (values row).2 ≤ rowRead) :
    (rowCoefficientsCosted costs omega values).2 ≤ rowPolynomialCoefficientsCostBudget costs n rowRead omega.2 :=
  rowCoefficientsCosted_cost_le costs omega values rowRead hvalues

/-- Actual public row providers and bounded stored private members keep every opening at the commitment width. -/
theorem denseOpeningPolynomialCosted_rowProviders_width (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (columns : List (List Fp)) (quotient linear : List Fp) (x1 : Fp × ℕ)
    (hcolumns : ∀ column ∈ columns, column.length ≤ 2048)
    (hquotient : quotient.length ≤ 2048) (hlinear : linear.length ≤ 2048) (group : Fin 5) :
    (denseOpeningPolynomialCosted equal read costs.add costs.multiply
      (fun action => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (instances action))
      (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (fixed column))
      (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (sigma column))
      columns (quotient, 1) (linear, 1) x1 group).1.length ≤ 2048 :=
  denseOpeningPolynomialCosted_length_le equal read costs.add costs.multiply
    (fun action => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (instances action))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (fixed column))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (sigma column))
    columns (quotient, 1) (linear, 1) x1 2048
    (fun action => (rowCoefficientsCosted_length costs (omegaOf 11, omegaAccess) (instances action)).le)
    (fun column => (rowCoefficientsCosted_length costs (omegaOf 11, omegaAccess) (fixed column)).le)
    (fun column => (rowCoefficientsCosted_length costs (omegaOf 11, omegaAccess) (sigma column)).le)
    hcolumns hquotient hlinear group

/-- The complete opening-fold bound follows from the actual public inverse DFTs and stored private capacities. -/
theorem denseOpeningPolynomialCosted_rowProviders_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (columns : List (List Fp)) (quotient linear : List Fp) (x1 : Fp × ℕ) (rowRead : ℕ)
    (hcolumns : ∀ column ∈ columns, column.length ≤ 2048)
    (hquotient : quotient.length ≤ 2048) (hlinear : linear.length ≤ 2048)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead) (group : Fin 5) :
    (denseOpeningPolynomialCosted equal read costs.add costs.multiply
      (fun action => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (instances action))
      (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (fixed column))
      (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (sigma column))
      columns (quotient, 1) (linear, 1) x1 group).2 ≤
      denseOpeningPolynomialCostBudget equal read costs.add costs.multiply actions columns.length
        (rowPolynomialCoefficientsCostBudget costs 2048 rowRead omegaAccess + 1) x1.2 2048 := by
  apply denseOpeningPolynomialCosted_cost_le
  · intro action; exact (rowCoefficientsCosted_length costs (omegaOf 11, omegaAccess) (instances action)).le
  · intro column; exact (rowCoefficientsCosted_length costs (omegaOf 11, omegaAccess) (fixed column)).le
  · intro column; exact (rowCoefficientsCosted_length costs (omegaOf 11, omegaAccess) (sigma column)).le
  · exact hcolumns
  · exact hquotient
  · exact hlinear
  · intro action; exact (rowPolynomialCoefficientsCosted_cost_le costs (omegaOf 11, omegaAccess)
      (instances action) rowRead (hinstances action)).trans (Nat.le_succ _)
  · intro column; exact (rowPolynomialCoefficientsCosted_cost_le costs (omegaOf 11, omegaAccess)
      (fixed column) rowRead (hfixed column)).trans (Nat.le_succ _)
  · intro column; exact (rowPolynomialCoefficientsCosted_cost_le costs (omegaOf 11, omegaAccess)
      (sigma column) rowRead (hsigma column)).trans (Nat.le_succ _)
  · exact Nat.le_add_left 1 _
  · exact Nat.le_add_left 1 _

end Zcash.Snark.ZeroKnowledge
