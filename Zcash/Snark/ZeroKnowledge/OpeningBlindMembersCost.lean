import Zcash.Snark.ZeroKnowledge.CollapsedQuotientPointCost
import Zcash.Snark.ZeroKnowledge.OpeningGroupLayoutCost
import Zcash.Snark.ZeroKnowledge.ScalarHornerCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Construct an opening group's actual blind list using the source's public ones and private slots. -/
def openingBlindMembersCosted (costs : FieldOperationCosts) (equal : ℕ) {actions : ℕ}
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x : Fp × ℕ) (group : Fin 5) : List Fp × ℕ :=
  Fin.cases
    (firstOpeningGroupCosted (fun _ : Fin actions => ((1 : Fp), 1))
      (fun action lookup => plonkColumnEntryCosted equal entries (.lookupTable action lookup))
      (fun _ : Fin 29 => ((1 : Fp), 1)) (fun _ : Fin 15 => ((1 : Fp), 1))
      (collapsedQuotientPointCosted costs.multiply costs.add costs.multiply x entries)
      (plonkLinearEntryCosted entries))
    (fun index =>
      let members := privateOpeningGroupCosted actions index
      let values := mapListCosted (plonkColumnEntryCosted equal entries) members.1
      (values.1, members.2 + values.2 + 1)) group

/-- Erasure gives precisely the blind component of the original paired polynomial list. -/
theorem openingBlindMembersCosted_result (costs : FieldOperationCosts) (equal : ℕ) {actions : ℕ}
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x : Fp × ℕ)
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) (group : Fin 5) :
    (openingBlindMembersCosted costs equal entries x group).1 =
      (plonkOpeningPairs pub rows x.1 pieces coefficients
        (plonkCommitmentBlindsFromVector (fun index => (entries index).1)) group).map Prod.snd := by
  refine Fin.cases ?_ (fun index => ?_) group
  · simp only [openingBlindMembersCosted, Fin.cases_zero, firstOpeningGroupCosted_result,
      plonkColumnEntryCosted_result, collapsedQuotientPointCosted_result, plonkLinearEntryCosted_result,
      plonkOpeningPairs, Fin.cons_zero, List.map_append, List.map_flatMap, List.map_map,
      List.map_cons, List.map_nil, Function.comp_def, plonkCommitmentBlindsFromVector,
      plonkCollapsedQuotientPoint, plonkCollapsedQuotientBlind, smul_eq_mul]
  · simp only [openingBlindMembersCosted, Fin.cases_succ, mapListCosted_result,
      privateOpeningGroupCosted_result, plonkColumnEntryCosted_result,
      plonkOpeningPairs, Fin.cons_succ, List.map_map, Function.comp_def, plonkCommitmentBlindsFromVector]

/-- The inherited blind list has exactly the original bounded group size. -/
theorem openingBlindMembersCosted_length_le (costs : FieldOperationCosts) (equal : ℕ) {actions : ℕ}
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x : Fp × ℕ) (group : Fin 5) :
    (openingBlindMembersCosted costs equal entries x group).1.length ≤ 9 * actions + 46 := by
  refine Fin.cases ?_ (fun index => ?_) group
  · change (firstOpeningGroupCosted _ _ _ _ _ _).1.length ≤ _
    rewrite [firstOpeningGroupCosted_length]
    omega
  · change (mapListCosted (plonkColumnEntryCosted equal entries)
      (privateOpeningGroupCosted actions index).1).1.length ≤ _
    rewrite [mapListCosted_result, List.length_map]
    exact (privateOpeningGroupCosted_length_le actions index).trans (Nat.le_add_right _ _)

end Zcash.Snark.ZeroKnowledge
