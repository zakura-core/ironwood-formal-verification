import Zcash.Snark.ZeroKnowledge.OpeningBlindMembersBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Construct and fold all inherited blinds of one original opening group. -/
def openingGroupBlindCosted (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ) (group : Fin 5) : Fp × ℕ :=
  let members := openingBlindMembersCosted costs equal entries x group
  let result := scalarHornerCosted read costs.add costs.multiply x1 members.1
  (result.1, members.2 + result.2 + 1)

/-- The computed blind is the actual source group blind, without an independence premise. -/
theorem openingGroupBlindCosted_result (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ)
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) (group : Fin 5) :
    (openingGroupBlindCosted costs equal read entries x x1 group).1 =
      (plonkBlindedOpeningGroup pub rows x.1 x1.1 pieces coefficients
        (plonkCommitmentBlindsFromVector (fun index => (entries index).1)) group).blind := by
  simp only [openingGroupBlindCosted, scalarHornerCosted_result,
    openingBlindMembersCosted_result costs equal entries x pub rows pieces coefficients,
    plonkBlindedOpeningGroup]

/-- Complete source-group blind preparation and fold budget. -/
def openingGroupBlindCostBudget (costs : FieldOperationCosts)
    (equal read actions access xRead x1Read : ℕ) : ℕ :=
  openingBlindMembersCostBudget costs equal actions access xRead +
    (9 * actions + 46) * (x1Read + read + costs.add + costs.multiply + 3) + 3

/-- The final blind bound retains all member preparation and every Horner operation. -/
theorem openingGroupBlindCosted_cost_le (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x x1 : Fp × ℕ) (access : ℕ)
    (hread : ∀ index, (entries index).2 ≤ access) (group : Fin 5) :
    (openingGroupBlindCosted costs equal read entries x x1 group).2 ≤
      openingGroupBlindCostBudget costs equal read actions access x.2 x1.2 := by
  have hm := openingBlindMembersCosted_cost_le costs equal entries x access hread group
  have hl := openingBlindMembersCosted_length_le costs equal entries x group
  have hf := scalarHornerCosted_cost_le read costs.add costs.multiply x1
    (openingBlindMembersCosted costs equal entries x group).1
  have hh := Nat.mul_le_mul_right (x1.2 + read + costs.add + costs.multiply + 3) hl
  change (openingBlindMembersCosted costs equal entries x group).2 +
    (scalarHornerCosted read costs.add costs.multiply x1 (openingBlindMembersCosted costs equal entries x group).1).2 + 1 ≤ _
  unfold openingGroupBlindCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
