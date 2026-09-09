import Zcash.Snark.ZeroKnowledge.PlonkOpeningMaterialCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Every materialized group has the original fixed coefficient and node capacities. -/
theorem plonkOpeningMaterialCosted_dimensions (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 constant slope : Fp × ℕ)
    (hpieces : ∀ piece ∈ pieces, piece.length ≤ 2048) (group : StoredOpeningGroup)
    (hgroup : group ∈ (plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces entries
      x x1 constant slope).1) :
    group.coefficients.length ≤ 2048 ∧ 0 < group.points.length ∧ group.points.length ≤ 3 := by
  unfold plonkOpeningMaterialCosted at hgroup
  exact storedPlonkOpeningGroupsCosted_dimensions costs equal read omegaAccess
    (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces x x1 constant slope).1
    entries x x1 2048
    (plonkOpeningPolynomialsFromRowsCosted_width costs equal read omegaAccess instances fixed sigma rows pieces
      x x1 constant slope hpieces) group hgroup

/-- Complete opening-material budget, including original polynomial preparation and all five group records. -/
def plonkOpeningMaterialCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns pieces rowRead entryRead xRead x1Read constantRead slopeRead : ℕ) : ℕ :=
  plonkOpeningPolynomialsFromRowsCostBudget costs equal read omegaAccess actions columns pieces
    rowRead xRead x1Read constantRead slopeRead +
    5 * (storedPlonkOpeningGroupCostBudget costs equal read omegaAccess actions 5 entryRead xRead x1Read + 1) + 27

/-- Actual row and blind readers discharge every cost in the complete original opening material. -/
theorem plonkOpeningMaterialCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 constant slope : Fp × ℕ) (rowRead entryRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ rowRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ rowRead)
    (hpieces : ∀ piece ∈ pieces, piece.length ≤ 2048)
    (hentries : ∀ index, (entries index).2 ≤ entryRead) :
    (plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces entries x x1 constant slope).2 ≤
      plonkOpeningMaterialCostBudget costs equal read omegaAccess actions rows.length pieces.length
        rowRead entryRead x.2 x1.2 constant.2 slope.2 := by
  have hp := plonkOpeningPolynomialsFromRowsCosted_cost_le costs equal read omegaAccess instances fixed sigma rows pieces
    x x1 constant slope rowRead hinstances hfixed hsigma hrows hpieces
  have hg := storedPlonkOpeningGroupsCosted_cost_le costs equal read omegaAccess
    (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces x x1 constant slope).1
    entries x x1 entryRead hentries
  rewrite [plonkOpeningPolynomialsFromRowsCosted_length] at hg
  unfold plonkOpeningMaterialCosted
  change (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces x x1 constant slope).2 +
    (storedPlonkOpeningGroupsCosted costs equal read omegaAccess
      (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces x x1 constant slope).1
      entries x x1).2 + 1 ≤ _
  unfold plonkOpeningMaterialCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
