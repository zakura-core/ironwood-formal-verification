import Zcash.Snark.ZeroKnowledge.OpeningBlindMembersCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- A common bound for actual public ones, routed private blinds, and the weighted quotient blind. -/
def openingBlindMemberAccessBudget (costs : FieldOperationCosts)
    (equal actions access xRead : ℕ) : ℕ :=
  1 + (4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + access + 13) +
    (8 * (access + xRead + 16384 * (costs.multiply + 1) + costs.multiply + costs.add + 8) + 65) +
    (access + 3)

/-- Complete original blind-list construction budget for either opening-group layout. -/
def openingBlindMembersCostBudget (costs : FieldOperationCosts)
    (equal actions access xRead : ℕ) : ℕ :=
  let member := openingBlindMemberAccessBudget costs equal actions access xRead
  (actions * actions + actions * (4 * member + 40) + 50 * member + 1200) +
    (actions * actions + 35 * actions + 9 * actions * (member + 1) + 3)

/-- Every inherited blind, original index calculation, bounded power, and list cell is counted. -/
theorem openingBlindMembersCosted_cost_le (costs : FieldOperationCosts) (equal : ℕ) {actions : ℕ}
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x : Fp × ℕ) (access : ℕ)
    (hread : ∀ index, (entries index).2 ≤ access) (group : Fin 5) :
    (openingBlindMembersCosted costs equal entries x group).2 ≤
      openingBlindMembersCostBudget costs equal actions access x.2 := by
  let member := openingBlindMemberAccessBudget costs equal actions access x.2
  have hone : 1 ≤ member := by dsimp only [member, openingBlindMemberAccessBudget]; omega
  have hcolumn (id : PrivateColumnId actions) : (plonkColumnEntryCosted equal entries id).2 ≤ member := by
    have h := plonkColumnEntryCosted_cost_le equal entries id access hread
    dsimp only [member, openingBlindMemberAccessBudget]
    omega
  have hquotient : (collapsedQuotientPointCosted costs.multiply costs.add costs.multiply x entries).2 ≤ member := by
    have h := collapsedQuotientPointCosted_cost_le costs.multiply costs.add costs.multiply x entries access hread
    dsimp only [member, openingBlindMemberAccessBudget]
    omega
  have hlinear : (plonkLinearEntryCosted entries).2 ≤ member := by
    have h := plonkLinearEntryCosted_cost_le entries access hread
    dsimp only [member, openingBlindMemberAccessBudget]
    omega
  refine Fin.cases ?_ (fun index => ?_) group
  · have h := firstOpeningGroupCosted_cost_le (fun _ : Fin actions => ((1 : Fp), 1))
      (fun action lookup => plonkColumnEntryCosted equal entries (.lookupTable action lookup))
      (fun _ : Fin 29 => ((1 : Fp), 1)) (fun _ : Fin 15 => ((1 : Fp), 1))
      (collapsedQuotientPointCosted costs.multiply costs.add costs.multiply x entries)
      (plonkLinearEntryCosted entries) member (fun _ => hone)
      (fun action lookup => hcolumn (.lookupTable action lookup)) (fun _ => hone) (fun _ => hone) hquotient hlinear
    exact h.trans (Nat.le_add_right _ _)
  · have hm := privateOpeningGroupCosted_cost_le actions index
    have hl := privateOpeningGroupCosted_length_le actions index
    have hv := mapListCosted_cost_le (plonkColumnEntryCosted equal entries)
      (privateOpeningGroupCosted actions index).1 member (fun id _ => hcolumn id)
    have hh := Nat.mul_le_mul_right (member + 1) hl
    change (privateOpeningGroupCosted actions index).2 +
      (mapListCosted (plonkColumnEntryCosted equal entries) (privateOpeningGroupCosted actions index).1).2 + 1 ≤ _
    change _ ≤ _ + (actions * actions + 35 * actions + 9 * actions * (member + 1) + 3)
    omega

end Zcash.Snark.ZeroKnowledge
