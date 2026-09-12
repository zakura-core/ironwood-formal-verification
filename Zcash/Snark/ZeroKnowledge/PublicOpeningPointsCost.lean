import Zcash.Snark.ZeroKnowledge.PublicOpeningClaimsCost
import Zcash.Snark.ZeroKnowledge.CollapsedQuotientPointCost

/-!
# Counted public opening commitments from original rows

Every public polynomial commitment includes inverse-DFT coefficient preparation.
The first group's table commitments and quotient pieces are routed through the
actual emitted slots. All supplied row, generator, and point-reader costs remain
in the bound.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Full public-row commitment budget, including the public polynomial's unit blind. -/
def publicRowCommitmentCostBudget (costs : FieldOperationCosts)
    (groupAdd groupScale rowRead generatorRead omegaAccess wAccess : ℕ) : ℕ :=
  2048 * (rowCoefficientCostBudget costs 2048 rowRead omegaAccess + generatorRead + groupScale + groupAdd + 2) +
    2048 * 2048 + 1 + wAccess + groupScale + groupAdd + 2

/-- Commit to a fixed-query row vector, counting its table routing and full coefficient preparation. -/
def fixedRowPointCosted (costs : FieldOperationCosts) (groupAdd groupScale omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (generators : Fin 2048 → G × ℕ)
    (W : G × ℕ) (query : Fin 29) : G × ℕ :=
  let index := fixedQueryOrderCosted query
  let point := rowPolynomialCommitmentCosted costs groupAdd groupScale (omegaOf 11, omegaAccess)
    (fixed index.1) generators W (1, 1)
  (point.1, index.2 + point.2 + 1)

/-- The fixed commitment agrees with the original polynomial commitment in the pinned query order. -/
theorem fixedRowPointCosted_result (costs : FieldOperationCosts) (groupAdd groupScale omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (generators : Fin 2048 → G × ℕ)
    (W : G × ℕ) (query : Fin 29) :
    (fixedRowPointCosted costs groupAdd groupScale omegaAccess fixed generators W query).1 =
      polynomialCommitment (fun index => (generators index).1) W.1
        (rowPolynomial (omegaOf 11) (fun row => (fixed (plonkFixedQueryOrder query) row).1)) 1 := by
  simp only [fixedRowPointCosted, fixedQueryOrderCosted_result,
    rowPolynomialCommitmentCosted_result costs groupAdd groupScale 11 (by decide)]
  all_goals rfl

/-- The fixed commitment bound includes the complete original query-table lookup. -/
theorem fixedRowPointCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (generators : Fin 2048 → G × ℕ)
    (W : G × ℕ) (query : Fin 29) (rowRead generatorRead : ℕ)
    (hread : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hgenerators : ∀ index, (generators index).2 ≤ generatorRead) :
    (fixedRowPointCosted costs groupAdd groupScale omegaAccess fixed generators W query).2 ≤
      publicRowCommitmentCostBudget costs groupAdd groupScale rowRead generatorRead omegaAccess W.2 + 120 := by
  have hindex := fixedQueryOrderCosted_cost_le query
  have hpoint := rowPolynomialCommitmentCosted_cost_le costs groupAdd groupScale (omegaOf 11, omegaAccess)
    (fixed (fixedQueryOrderCosted query).1) generators W (1, 1) rowRead generatorRead (hread _) hgenerators
  dsimp only at hpoint
  simp only [fixedRowPointCosted, publicRowCommitmentCostBudget]
  omega

/-- Construct all public-group commitments, with original row preparation and emitted-point routing. -/
def firstPublicOpeningPointsCosted (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (x : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) : List G × ℕ :=
  firstOpeningGroupCosted
    (fun action => rowPolynomialCommitmentCosted costs groupAdd groupScale (omegaOf 11, omegaAccess)
      (instances action) generators W (1, 1))
    (fun action lookup => plonkColumnEntryCosted equal points (.lookupTable action lookup))
    (fixedRowPointCosted costs groupAdd groupScale omegaAccess fixed generators W)
    (fun index => rowPolynomialCommitmentCosted costs groupAdd groupScale (omegaOf 11, omegaAccess)
      (sigma index) generators W (1, 1))
    (collapsedQuotientPointCosted costs.multiply groupAdd groupScale x points)
    (plonkLinearEntryCosted points)

/-- Erasure is the first commitment group for exactly these public rows and setup points. -/
theorem firstPublicOpeningPointsCosted_result (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (U : G)
    (x : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ) :
    (firstPublicOpeningPointsCosted costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x points).1 =
      plonkPublicCommitmentMembers
        { k := 11, g := fun index => (generators index).1, w := W.1, u := U }
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        x.1 (fun index => (points index).1) 0 := by
  simp only [firstPublicOpeningPointsCosted, firstOpeningGroupCosted_result, fixedRowPointCosted_result,
    rowPolynomialCommitmentCosted_result costs groupAdd groupScale 11 (by decide),
    plonkColumnEntryCosted_result, collapsedQuotientPointCosted_result, plonkLinearEntryCosted_result,
    plonkPublicCommitmentMembers, plonkPublicPolynomialsFromRows, Fin.cons_zero]
  all_goals rfl

/-- Member-production budget derived from counted row commitments and emitted-point operations. -/
def publicOpeningPointAccessBudget (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess actions rowRead generatorRead wAccess pointRead xAccess : ℕ) : ℕ :=
  publicRowCommitmentCostBudget costs groupAdd groupScale rowRead generatorRead omegaAccess wAccess +
    (4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + pointRead + 13) +
    (8 * (pointRead + xAccess + 16384 * (costs.multiply + 1) + groupScale + groupAdd + 8) + 65) +
    pointRead + 3 + 120

/-- Every member's complete production cost is discharged in the first-group bound. -/
theorem firstPublicOpeningPointsCosted_cost_le (costs : FieldOperationCosts)
    (groupAdd groupScale equal omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (x : Fp × ℕ) (points : Fin (22 * actions + 10) → G × ℕ)
    (rowRead generatorRead pointRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hgenerators : ∀ index, (generators index).2 ≤ generatorRead)
    (hpoints : ∀ index, (points index).2 ≤ pointRead) :
    let access := publicOpeningPointAccessBudget costs groupAdd groupScale equal omegaAccess actions
      rowRead generatorRead W.2 pointRead x.2
    (firstPublicOpeningPointsCosted costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W x points).2 ≤
      actions * actions + actions * (4 * access + 40) + 50 * access + 1200 := by
  dsimp only
  apply firstOpeningGroupCosted_cost_le
  · intro action
    have h := rowPolynomialCommitmentCosted_cost_le costs groupAdd groupScale (omegaOf 11, omegaAccess)
      (instances action) generators W (1, 1) rowRead generatorRead (hinstances action) hgenerators
    dsimp only at h
    dsimp only [publicOpeningPointAccessBudget, publicRowCommitmentCostBudget]
    omega
  · intro action lookup
    have h := plonkColumnEntryCosted_cost_le equal points (PrivateColumnId.lookupTable action lookup) pointRead hpoints
    dsimp only [publicOpeningPointAccessBudget]
    omega
  · intro query
    have h := fixedRowPointCosted_cost_le costs groupAdd groupScale omegaAccess fixed generators W query
      rowRead generatorRead hfixed hgenerators
    dsimp only [publicOpeningPointAccessBudget]
    omega
  · intro index
    have h := rowPolynomialCommitmentCosted_cost_le costs groupAdd groupScale (omegaOf 11, omegaAccess)
      (sigma index) generators W (1, 1) rowRead generatorRead (hsigma index) hgenerators
    dsimp only at h
    dsimp only [publicOpeningPointAccessBudget, publicRowCommitmentCostBudget]
    omega
  · have h := collapsedQuotientPointCosted_cost_le costs.multiply groupAdd groupScale x points pointRead hpoints
    dsimp only [publicOpeningPointAccessBudget]
    omega
  · have h := plonkLinearEntryCosted_cost_le points pointRead hpoints
    dsimp only [publicOpeningPointAccessBudget]
    omega

end Zcash.Snark.ZeroKnowledge
