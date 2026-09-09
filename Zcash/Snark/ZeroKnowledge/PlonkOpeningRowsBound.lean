import Zcash.Snark.ZeroKnowledge.PlonkOpeningRowsCapacity

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)

attribute [local irreducible] privatePolynomialCoefficientsCosted rowCoefficientsCosted

/-- Fixed full-opening budget from original row and piece storage, with every preparatory computation retained. -/
def plonkOpeningPolynomialsFromRowsCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns pieces rowRead xRead x1Read constantRead slopeRead : ℕ) : ℕ :=
  (columns * (2048 * (rowCoefficientCostBudget costs 2048 rowRead omegaAccess + 1) +
    2048 * 2048 + 2) + 1) +
    denseWeightedSumCostBudget read costs.add costs.multiply xRead 2048 8 2048 (2 * pieces + read + 1) +
    (constantRead + slopeRead + 3) +
    (5 * (denseOpeningPolynomialCostBudget equal read costs.add costs.multiply actions columns
      (rowPolynomialCoefficientsCostBudget costs 2048 rowRead omegaAccess + 1) x1Read 2048 + 1) + 26) + 3

/-- The complete five-polynomial construction is bounded from actual row readers and stored pieces. -/
theorem plonkOpeningPolynomialsFromRowsCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (x x1 constant slope : Fp × ℕ) (rowRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ rowRead)
    (hpieces : ∀ piece ∈ pieces, piece.length ≤ 2048) :
    (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces
      x x1 constant slope).2 ≤
      plonkOpeningPolynomialsFromRowsCostBudget costs equal read omegaAccess actions rows.length pieces.length
        rowRead x.2 x1.2 constant.2 slope.2 := by
  let columns := privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows
  let quotient := denseCollapsedQuotientCosted read costs.add costs.multiply x
    (fun index => getDListCosted read [] pieces index.val)
  let linear := denseLinearMaskCosted constant slope
  let producer := fun group => denseOpeningPolynomialCosted equal read costs.add costs.multiply
    (fun action => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (instances action))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (fixed column))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (sigma column))
    columns.1 (quotient.1, 1) (linear.1, 1) x1 group
  have hc := privatePolynomialCoefficientsCosted_cost_le costs (omegaOf 11, omegaAccess) rows rowRead hrows
  have hq := denseCollapsedQuotientCosted_stored_cost_le read costs.add costs.multiply x pieces 2048 hpieces
  have hcw : ∀ column ∈ columns.1, column.length ≤ 2048 := fun column hcolumn =>
    (privatePolynomialCoefficientsCosted_width costs (omegaOf 11, omegaAccess) rows column hcolumn).le
  have hqw : quotient.1.length ≤ 2048 :=
    denseCollapsedQuotientCosted_stored_width read costs.add costs.multiply x pieces 2048 hpieces
  have hlw : linear.1.length ≤ 2048 := (denseLinearMaskCosted_length constant slope).le.trans (by decide)
  let groupBudget := denseOpeningPolynomialCostBudget equal read costs.add costs.multiply actions rows.length
    (rowPolynomialCoefficientsCostBudget costs 2048 rowRead omegaAccess + 1) x1.2 2048
  have hg (group : Fin 5) : (producer group).2 ≤ groupBudget := by
    have h := denseOpeningPolynomialCosted_rowProviders_cost_le costs equal read omegaAccess instances fixed sigma
      columns.1 quotient.1 linear.1 x1 rowRead hcw hqw hlw hinstances hfixed hsigma group
    change (producer group).2 ≤ denseOpeningPolynomialCostBudget equal read costs.add costs.multiply actions
      (privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows).1.length
      (rowPolynomialCoefficientsCostBudget costs 2048 rowRead omegaAccess + 1) x1.2 2048 at h
    rewrite [privatePolynomialCoefficientsCosted_length] at h
    exact h
  have hf := ofFnCosted_cost_le producer groupBudget hg
  have hl : linear.2 = constant.2 + slope.2 + 3 := rfl
  unfold plonkOpeningPolynomialsFromRowsCosted
  change columns.2 + quotient.2 + linear.2 + (ofFnCosted producer).2 + 3 ≤ _
  change columns.2 ≤ rows.length * (2048 * (rowCoefficientCostBudget costs 2048 rowRead omegaAccess + 1) +
    2048 * 2048 + 2) + 1 at hc
  change quotient.2 ≤ denseWeightedSumCostBudget read costs.add costs.multiply x.2 2048 8 2048
    (2 * pieces.length + read + 1) at hq
  change (ofFnCosted producer).2 ≤ 5 * (groupBudget + 1) + 26 at hf
  rewrite [hl]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hc hq)
    (constant.2 + slope.2 + 3)) hf) 3

end Zcash.Snark.ZeroKnowledge
