import Zcash.Snark.ZeroKnowledge.DenseOpeningPolynomialCost
import Zcash.Snark.ZeroKnowledge.DenseCollapsedQuotientCost
import Zcash.Snark.ZeroKnowledge.PlonkPublicRows

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark CompPoly
open Zcash.Arithmetic (Fp omegaOf)

attribute [local irreducible] privatePolynomialCoefficientsCosted rowCoefficientsCosted
attribute [local irreducible] rowPolynomial densePolynomial

/-- Prepare the actual public/private polynomials, collapse the stored quotient pieces, and construct all five openings. -/
@[irreducible] def plonkOpeningPolynomialsFromRowsCosted (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (x x1 constant slope : Fp × ℕ) : List (List Fp) × ℕ :=
  let columns := privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows
  let quotient := denseCollapsedQuotientCosted read costs.add costs.multiply x
    (fun index => getDListCosted read [] pieces index.val)
  let linear := denseLinearMaskCosted constant slope
  let result := ofFnCosted (fun group => denseOpeningPolynomialCosted equal read costs.add costs.multiply
    (fun action => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (instances action))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (fixed column))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (sigma column))
    columns.1 (quotient.1, 1) (linear.1, 1) x1 group)
  (result.1, columns.2 + quotient.2 + linear.2 + result.2 + 3)

/-- Full erasure recovers the original five opening polynomials from the same rows, pieces, and linear mask. -/
theorem plonkOpeningPolynomialsFromRowsCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (x x1 constant slope : Fp × ℕ) :
    ((plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces
      x x1 constant slope).1.map densePolynomial) =
      List.ofFn (plonkOpeningPolynomials
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        (rows.map (fun column row => (column row).1)) x.1 x1.1
        (fun index => densePolynomial (pieces.getD index.val [])) (constant.1, slope.1)) := by
  let columns := privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows
  let quotient := denseCollapsedQuotientCosted read costs.add costs.multiply x
    (fun index => getDListCosted read [] pieces index.val)
  let linear := denseLinearMaskCosted constant slope
  unfold plonkOpeningPolynomialsFromRowsCosted
  change ((ofFnCosted (fun group => denseOpeningPolynomialCosted equal read costs.add costs.multiply
    (fun action => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (instances action))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (fixed column))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (sigma column))
    columns.1 (quotient.1, 1) (linear.1, 1) x1 group)).1.map densePolynomial) = _
  rewrite [ofFnCosted_result, List.map_ofFn]
  apply congrArg List.ofFn
  funext group
  apply denseOpeningPolynomialCosted_result equal read costs.add costs.multiply
    (fun action => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (instances action))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (fixed column))
    (fun column => rowCoefficientsCosted costs (omegaOf 11, omegaAccess) (sigma column))
    columns.1 (quotient.1, 1) (linear.1, 1) x1
    (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
      (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
    (rows.map (fun column row => (column row).1)) x.1
    (fun index => densePolynomial (pieces.getD index.val [])) (constant.1, slope.1)
    (by intro action; simpa only [plonkPublicPolynomialsFromRows] using
      densePolynomial_rowCoefficientsCosted costs 11 (by decide) omegaAccess (instances action))
    (by intro column; simpa only [plonkPublicPolynomialsFromRows] using
      densePolynomial_rowCoefficientsCosted costs 11 (by decide) omegaAccess (fixed column))
    (by intro column; simpa only [plonkPublicPolynomialsFromRows] using
      densePolynomial_rowCoefficientsCosted costs 11 (by decide) omegaAccess (sigma column))
    (fun id => privateColumnCoefficientsCosted_from_rows costs equal read omegaAccess rows id)
    ?_ (denseLinearMaskCosted_result constant slope) group
  change densePolynomial (denseCollapsedQuotientCosted read costs.add costs.multiply x
    (fun index => getDListCosted read [] pieces index.val)).1 = _
  rewrite [denseCollapsedQuotientCosted_result]
  simp only [getDListCosted_result]

/-- Every execution materializes exactly the five original opening polynomials. -/
theorem plonkOpeningPolynomialsFromRowsCosted_length (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (x x1 constant slope : Fp × ℕ) :
    (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces
      x x1 constant slope).1.length = 5 := by
  have h := congrArg List.length (plonkOpeningPolynomialsFromRowsCosted_result costs equal read omegaAccess
    instances fixed sigma rows pieces x x1 constant slope)
  simpa only [List.length_map, List.length_ofFn] using h

end Zcash.Snark.ZeroKnowledge
