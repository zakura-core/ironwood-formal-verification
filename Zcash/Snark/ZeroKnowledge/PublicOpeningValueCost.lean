import Zcash.Snark.ZeroKnowledge.PublicOpeningClaimsCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost

/-!
# Counted first-group scalar folding

The public claim list includes the counted row-polynomial preparation and actual
query routing. This module folds that materialized list with the original scalar
Horner rule, including all challenge accesses, field arithmetic, and list reads.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- The complete public claim list has the exact original group length. -/
theorem firstPublicOpeningClaimsCosted_length (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x hEval rEval : Fp × ℕ) :
    (firstPublicOpeningClaimsCosted costs equal read omegaAccess instances fixed sigma views x hEval rEval).1.length =
      4 * actions + 46 := by
  unfold firstPublicOpeningClaimsCosted
  exact firstOpeningGroupCosted_length _ _ _ _ _ _

/-- Construct and fold the first group's complete public scalar claims. -/
def firstPublicOpeningValueCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x x1 hEval rEval : Fp × ℕ) : Fp × ℕ :=
  let claims := firstPublicOpeningClaimsCosted costs equal read omegaAccess instances fixed sigma views x hEval rEval
  let value := foldlCosted (fun state value =>
    (state * x1.1 + value, x1.2 + costs.multiply + costs.add + 2)) claims.1 (0, 1)
  (value.1, claims.2 + value.2 + 1)

/-- Erasure is the original first-group scalar fold over the exact public claim list. -/
theorem firstPublicOpeningValueCosted_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x x1 hEval rEval : Fp × ℕ) :
    (firstPublicOpeningValueCosted costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval).1 =
      plonkScalarFold x1.1 (plonkFirstGroupClaims
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        x.1 (privateColumnView (views.map (fun column index => (column index).1))) hEval.1 rEval.1) := by
  simp only [firstPublicOpeningValueCosted, foldlCosted_result, firstPublicOpeningClaimsCosted_result,
    plonkScalarFold]

/-- The full scalar-fold bound retains all claim preparation and routing costs. -/
theorem firstPublicOpeningValueCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x x1 hEval rEval : Fp × ℕ)
    (rowRead observationRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hviews : ∀ column ∈ views, ∀ index, (column index).2 ≤ observationRead) :
    let access := publicOpeningClaimAccessBudget costs equal read omegaAccess actions views.length
      rowRead observationRead x.2 hEval.2 rEval.2
    (firstPublicOpeningValueCosted costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval).2 ≤
      actions * actions + actions * (4 * access + 40) + 50 * access + 1200 +
        (4 * actions + 46) * (x1.2 + costs.multiply + costs.add + 3) + 3 := by
  let claims := firstPublicOpeningClaimsCosted costs equal read omegaAccess instances fixed sigma views x hEval rEval
  let step := fun (state value : Fp) => (state * x1.1 + value, x1.2 + costs.multiply + costs.add + 2)
  have hfold := foldlCosted_cost_le_sum step claims.1 (0, 1) (fun _ => True)
    (fun _ => x1.2 + costs.multiply + costs.add + 2)
    trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => le_rfl)
  have hlength : claims.1.length = 4 * actions + 46 :=
    firstPublicOpeningClaimsCosted_length costs equal read omegaAccess instances fixed sigma views x hEval rEval
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, hlength] at hfold
  have hclaims := firstPublicOpeningClaimsCosted_cost_le costs equal read omegaAccess
    instances fixed sigma views x hEval rEval rowRead observationRead hinstances hfixed hsigma hviews
  dsimp only
  change claims.2 + (foldlCosted step claims.1 (0, 1)).2 + 1 ≤ _
  nlinarith

end Zcash.Snark.ZeroKnowledge
