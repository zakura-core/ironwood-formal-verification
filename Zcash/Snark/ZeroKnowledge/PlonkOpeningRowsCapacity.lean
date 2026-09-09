import Zcash.Snark.ZeroKnowledge.OpeningRowProviderBounds

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)

attribute [local irreducible] privatePolynomialCoefficientsCosted rowCoefficientsCosted

/-- Defaulted piece reads preserve the supplied coefficient capacity. -/
theorem denseCollapsedQuotientCosted_stored_width (read add multiply : ℕ) (x : Fp × ℕ)
    (pieces : List (List Fp)) (width : ℕ) (hpieces : ∀ piece ∈ pieces, piece.length ≤ width) :
    (denseCollapsedQuotientCosted read add multiply x
      (fun index => getDListCosted read [] pieces index.val)).1.length ≤ width :=
  denseCollapsedQuotientCosted_length_le read add multiply x
    (fun index => getDListCosted read [] pieces index.val) width
    (fun index => getDListCosted_property read [] pieces (fun piece => piece.length ≤ width)
      (Nat.zero_le _) hpieces index.val)

/-- The actual stored piece reader supplies all eight quotient-collapse access bounds. -/
theorem denseCollapsedQuotientCosted_stored_cost_le (read add multiply : ℕ) (x : Fp × ℕ)
    (pieces : List (List Fp)) (width : ℕ) (hpieces : ∀ piece ∈ pieces, piece.length ≤ width) :
    (denseCollapsedQuotientCosted read add multiply x
      (fun index => getDListCosted read [] pieces index.val)).2 ≤
      denseWeightedSumCostBudget read add multiply x.2 2048 8 width (2 * pieces.length + read + 1) :=
  denseCollapsedQuotientCosted_cost_le read add multiply x
    (fun index => getDListCosted read [] pieces index.val) width (2 * pieces.length + read + 1)
    (fun index => getDListCosted_property read [] pieces (fun piece => piece.length ≤ width)
      (Nat.zero_le _) hpieces index.val)
    (fun index => getDListCosted_cost_le read [] pieces index.val)

/-- All five openings constructed from original rows fit the complete IPA commitment-vector capacity. -/
theorem plonkOpeningPolynomialsFromRowsCosted_width (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (x x1 constant slope : Fp × ℕ) (hpieces : ∀ piece ∈ pieces, piece.length ≤ 2048)
    (poly : List Fp) (hpoly : poly ∈
      (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces
        x x1 constant slope).1) : poly.length ≤ 2048 := by
  let columns := privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows
  let quotient := denseCollapsedQuotientCosted read costs.add costs.multiply x
    (fun index => getDListCosted read [] pieces index.val)
  let linear := denseLinearMaskCosted constant slope
  unfold plonkOpeningPolynomialsFromRowsCosted at hpoly
  change poly ∈ (ofFnCosted (fun group => denseOpeningPolynomialCosted equal read costs.add costs.multiply
    (fun action => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (instances action))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (fixed column))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (sigma column))
    columns.1 (quotient.1, 1) (linear.1, 1) x1 group)).1 at hpoly
  simp only [ofFnCosted_result, List.mem_ofFn] at hpoly
  obtain ⟨group, rfl⟩ := hpoly
  apply denseOpeningPolynomialCosted_rowProviders_width costs equal read omegaAccess instances fixed sigma
    columns.1 quotient.1 linear.1 x1
  · intro column hcolumn
    exact (privatePolynomialCoefficientsCosted_width costs (omegaOf 11, omegaAccess) rows column hcolumn).le
  · exact denseCollapsedQuotientCosted_stored_width read costs.add costs.multiply x pieces 2048 hpieces
  · exact (denseLinearMaskCosted_length constant slope).le.trans (by decide)

end Zcash.Snark.ZeroKnowledge
