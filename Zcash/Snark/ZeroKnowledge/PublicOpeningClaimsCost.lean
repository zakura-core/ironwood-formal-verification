import Zcash.Snark.ZeroKnowledge.OpeningGroupLayoutCost
import Zcash.Snark.ZeroKnowledge.QueryOrderCost
import Zcash.Snark.ZeroKnowledge.RowPolynomialCost
import Zcash.Snark.ZeroKnowledge.PrivateColumnRoutingCost
import Zcash.Snark.ZeroKnowledge.PlonkPublicRows
import Zcash.Snark.ZeroKnowledge.PlonkPublicOpening

/-!
# Counted public opening claims from original rows

Public polynomial evaluations include their inverse-DFT coefficient preparation.
The fixed-query table and private lookup-table disclosures use their counted
routers. The final list is exactly the original first opening group's claims.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)

/-- The checked row-evaluation budget at the protocol's 2048-row domain. -/
def publicRowEvaluationCostBudget (costs : FieldOperationCosts) (rowRead omegaAccess pointAccess : ℕ) : ℕ :=
  2048 * (rowCoefficientCostBudget costs 2048 rowRead omegaAccess + pointAccess +
    2048 * (costs.multiply + 1) + costs.multiply + costs.add + 3) + 2048 * 2048 + 1

/-- Evaluate a fixed query while counting both query-order routing and polynomial preparation. -/
def fixedRowEvaluationCosted (costs : FieldOperationCosts) (omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (query : Fin 29) : Fp × ℕ :=
  let index := fixedQueryOrderCosted query
  let value := rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (fixed index.1) point
  (value.1, index.2 + value.2 + 1)

/-- The fixed-query result is the original canonical polynomial evaluation in the pinned order. -/
theorem fixedRowEvaluationCosted_result (costs : FieldOperationCosts) (omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (query : Fin 29) :
    (fixedRowEvaluationCosted costs omegaAccess fixed point query).1 =
      (rowPolynomial (omegaOf 11) (fun row => (fixed (plonkFixedQueryOrder query) row).1)).eval point.1 := by
  simp only [fixedRowEvaluationCosted, fixedQueryOrderCosted_result,
    rowPolynomialEvalCosted_result costs 11 (by decide)]
  rfl

/-- The fixed-query bound includes construction and search of the actual query table. -/
theorem fixedRowEvaluationCosted_cost_le (costs : FieldOperationCosts) (omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (query : Fin 29)
    (rowRead : ℕ) (hread : ∀ column row, (fixed column row).2 ≤ rowRead) :
    (fixedRowEvaluationCosted costs omegaAccess fixed point query).2 ≤
      publicRowEvaluationCostBudget costs rowRead omegaAccess point.2 + 120 := by
  have hindex := fixedQueryOrderCosted_cost_le query
  have hvalue := rowPolynomialEvalCosted_cost_le costs (omegaOf 11, omegaAccess)
    (fixed (fixedQueryOrderCosted query).1) point rowRead (hread _)
  dsimp only at hvalue
  simp only [fixedRowEvaluationCosted, publicRowEvaluationCostBudget]
  omega

/-- Construct all first-group claims from public rows and the disclosed private view. -/
def firstPublicOpeningClaimsCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x hEval rEval : Fp × ℕ) : List Fp × ℕ :=
  firstOpeningGroupCosted
    (fun action => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (instances action) x)
    (fun action lookup => privateColumnViewCosted equal read views (.lookupTable action lookup) 0)
    (fixedRowEvaluationCosted costs omegaAccess fixed x)
    (fun index => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (sigma index) x)
    hEval rEval

/-- Erasure is the complete original first-group claim list, with the supplied quotient value. -/
theorem firstPublicOpeningClaimsCosted_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x hEval rEval : Fp × ℕ) :
    (firstPublicOpeningClaimsCosted costs equal read omegaAccess instances fixed sigma views x hEval rEval).1 =
      plonkFirstGroupClaims
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        x.1 (privateColumnView (views.map (fun column index => (column index).1))) hEval.1 rEval.1 := by
  simp only [firstPublicOpeningClaimsCosted, firstOpeningGroupCosted_result, fixedRowEvaluationCosted_result,
    rowPolynomialEvalCosted_result costs 11 (by decide), privateColumnViewCosted_result,
    plonkFirstGroupClaims, plonkPublicPolynomialsFromRows]
  rfl

/-- Member-production budget derived from the counted public and private computations. -/
def publicOpeningClaimAccessBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns rowRead observationRead pointAccess hAccess rAccess : ℕ) : ℕ :=
  publicRowEvaluationCostBudget costs rowRead omegaAccess pointAccess +
    (4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
      2 * columns + read + observationRead + 15) + hAccess + rAccess + 120

/-- The full public-group bound discharges every member cost from its actual counted implementation. -/
theorem firstPublicOpeningClaimsCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x hEval rEval : Fp × ℕ)
    (rowRead observationRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hviews : ∀ column ∈ views, ∀ index, (column index).2 ≤ observationRead) :
    let access := publicOpeningClaimAccessBudget costs equal read omegaAccess actions views.length
      rowRead observationRead x.2 hEval.2 rEval.2
    (firstPublicOpeningClaimsCosted costs equal read omegaAccess instances fixed sigma views x hEval rEval).2 ≤
      actions * actions + actions * (4 * access + 40) + 50 * access + 1200 := by
  dsimp only
  apply firstOpeningGroupCosted_cost_le
  · intro action
    have h := rowPolynomialEvalCosted_cost_le costs (omegaOf 11, omegaAccess) (instances action) x
      rowRead (hinstances action)
    dsimp only at h
    dsimp only [publicOpeningClaimAccessBudget, publicRowEvaluationCostBudget]
    omega
  · intro action lookup
    have h := privateColumnViewCosted_cost_le equal read views
      (PrivateColumnId.lookupTable action lookup) 0 observationRead hviews
    dsimp only [publicOpeningClaimAccessBudget]
    omega
  · intro query
    have h := fixedRowEvaluationCosted_cost_le costs omegaAccess fixed x query rowRead hfixed
    dsimp only [publicOpeningClaimAccessBudget]
    omega
  · intro index
    have h := rowPolynomialEvalCosted_cost_le costs (omegaOf 11, omegaAccess) (sigma index) x
      rowRead (hsigma index)
    dsimp only at h
    dsimp only [publicOpeningClaimAccessBudget, publicRowEvaluationCostBudget]
    omega
  · dsimp only [publicOpeningClaimAccessBudget]; omega
  · dsimp only [publicOpeningClaimAccessBudget]; omega

end Zcash.Snark.ZeroKnowledge
