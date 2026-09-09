import Zcash.Snark.ZeroKnowledge.PlonkOpeningRowsBound
import Zcash.Snark.ZeroKnowledge.StoredPlonkOpeningGroupsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Construct the complete opening material from actual rows, stored quotient pieces, and inherited blinds. -/
@[irreducible] def plonkOpeningMaterialCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 constant slope : Fp × ℕ) : List StoredOpeningGroup × ℕ :=
  let polynomials := plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces
    x x1 constant slope
  let groups := storedPlonkOpeningGroupsCosted costs equal read omegaAccess polynomials.1 entries x x1
  (groups.1, polynomials.2 + groups.2 + 1)

/-- Full opening-material erasure identifies the exact original rows, pieces, mask, and blind vector. -/
theorem plonkOpeningMaterialCosted_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 constant slope : Fp × ℕ) :
    ((plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces entries
      x x1 constant slope).1.map StoredOpeningGroup.erase) =
      plonkBlindedOpeningGroups
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        (rows.map (fun column row => (column row).1)) x.1 x1.1
        (fun index => densePolynomial (pieces.getD index.val [])) (constant.1, slope.1)
        (plonkCommitmentBlindsFromVector (fun index => (entries index).1)) := by
  unfold plonkOpeningMaterialCosted
  exact storedPlonkOpeningGroupsCosted_result costs equal read omegaAccess
    (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces x x1 constant slope).1
    entries x x1 _ _ _ _
    (plonkOpeningPolynomialsFromRowsCosted_result costs equal read omegaAccess instances fixed sigma rows pieces
      x x1 constant slope)

/-- The complete material contains precisely the original five groups. -/
theorem plonkOpeningMaterialCosted_length (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 constant slope : Fp × ℕ) :
    (plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces entries
      x x1 constant slope).1.length = 5 := by
  unfold plonkOpeningMaterialCosted
  exact storedPlonkOpeningGroupsCosted_length costs equal read omegaAccess
    (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces x x1 constant slope).1
    entries x x1

/-- Actual group preparation preserves the source point-count bound independently of all row and field values. -/
theorem plonkOpeningMaterialCosted_points (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (pieces : List (List Fp))
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 constant slope : Fp × ℕ)
    (group : StoredOpeningGroup) (hgroup : group ∈
      (plonkOpeningMaterialCosted costs equal read omegaAccess instances fixed sigma rows pieces entries x x1 constant slope).1) :
    0 < group.points.length ∧ group.points.length ≤ 3 := by
  unfold plonkOpeningMaterialCosted at hgroup
  exact storedPlonkOpeningGroupsCosted_points costs equal read omegaAccess
    (plonkOpeningPolynomialsFromRowsCosted costs equal read omegaAccess instances fixed sigma rows pieces x x1 constant slope).1
    entries x x1 group hgroup

end Zcash.Snark.ZeroKnowledge
