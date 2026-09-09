import Zcash.Snark.ZeroKnowledge.OpeningGroupBlindCost
import Zcash.Snark.ZeroKnowledge.OpeningPointSetsCost
import Zcash.Snark.ZeroKnowledge.StoredOpeningGroup
import Zcash.Snark.ZeroKnowledge.PrivatePolynomialCoefficientsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

attribute [local irreducible] densePolynomial rowPolynomial plonkOpeningPolynomials

/-- Assemble one complete original opening group from stored coefficients, actual points, and inherited blinds. -/
def storedPlonkOpeningGroupCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ)
    (x x1 : Fp × ℕ) (index : Fin 5) : StoredOpeningGroup × ℕ :=
  let polynomial := getDListCosted read [] polynomials index.val
  let points := openingPointSetCosted costs (omegaOf 11, omegaAccess) x index
  let blind := openingGroupBlindCosted costs equal read entries x x1 index
  (⟨polynomial.1, points.1, blind.1⟩, polynomial.2 + points.2 + blind.2 + 3)

/-- Exact coefficient storage supplies the original complete group, with the same point and blind routing. -/
theorem storedPlonkOpeningGroupCosted_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ)
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp)
    (hpolynomials : polynomials.map densePolynomial = List.ofFn (plonkOpeningPolynomials pub rows x.1 x1.1 pieces coefficients))
    (index : Fin 5) :
    (storedPlonkOpeningGroupCosted costs equal read omegaAccess polynomials entries x x1 index).1.erase =
      plonkBlindedOpeningGroup pub rows x.1 x1.1 pieces coefficients
        (plonkCommitmentBlindsFromVector (fun i => (entries i).1)) index := by
  have hp : densePolynomial (polynomials.getD index.val []) =
      plonkOpeningPolynomials pub rows x.1 x1.1 pieces coefficients index := by
    rewrite [densePolynomial_getD, hpolynomials,
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using index.isLt), List.getElem_ofFn]
    rfl
  simp only [storedPlonkOpeningGroupCosted, StoredOpeningGroup.erase, getDListCosted_result,
    openingPointSetCosted_result,
    openingGroupBlindCosted_result costs equal read entries x x1 pub rows pieces coefficients, hp,
    plonkBlindedOpeningGroup]

/-- Stored group assembly preserves the common polynomial coefficient capacity. -/
theorem storedPlonkOpeningGroupCosted_width (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ)
    (width : ℕ) (hpolynomials : ∀ poly ∈ polynomials, poly.length ≤ width) (index : Fin 5) :
    (storedPlonkOpeningGroupCosted costs equal read omegaAccess polynomials entries x x1 index).1.coefficients.length ≤ width :=
  getDListCosted_property read [] polynomials (fun poly => poly.length ≤ width) (Nat.zero_le _) hpolynomials index.val

/-- The original one-to-three-node layout is retained, even when field values coincide. -/
theorem storedPlonkOpeningGroupCosted_points (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ) (index : Fin 5) :
    0 < (storedPlonkOpeningGroupCosted costs equal read omegaAccess polynomials entries x x1 index).1.points.length ∧
      (storedPlonkOpeningGroupCosted costs equal read omegaAccess polynomials entries x x1 index).1.points.length ≤ 3 :=
  openingPointSetCosted_length costs (omegaOf 11, omegaAccess) x index

/-- Complete stored group assembly budget. -/
def storedPlonkOpeningGroupCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions polynomials access xRead x1Read : ℕ) : ℕ :=
  (2 * polynomials + read + 1) +
    (3 * (xRead + omegaAccess + 7 * (costs.multiply + 1) + costs.inverse + 14) + 18) +
    openingGroupBlindCostBudget costs equal read actions access xRead x1Read + 3

/-- Actual point preparation and blind folding discharge every group assembly producer cost. -/
theorem storedPlonkOpeningGroupCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (polynomials : List (List Fp)) (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ)
    (access : ℕ) (hread : ∀ index, (entries index).2 ≤ access) (index : Fin 5) :
    (storedPlonkOpeningGroupCosted costs equal read omegaAccess polynomials entries x x1 index).2 ≤
      storedPlonkOpeningGroupCostBudget costs equal read omegaAccess actions polynomials.length access x.2 x1.2 := by
  have hp := getDListCosted_cost_le read [] polynomials index.val
  have hn := openingPointSetCosted_cost_le costs (omegaOf 11, omegaAccess) x index
  have hb := openingGroupBlindCosted_cost_le costs equal read entries x x1 access hread index
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp hn) hb) 3

end Zcash.Snark.ZeroKnowledge
