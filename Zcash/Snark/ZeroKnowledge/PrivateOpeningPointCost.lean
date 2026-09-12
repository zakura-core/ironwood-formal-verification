import Zcash.Snark.ZeroKnowledge.OpeningGroupLayoutCost
import Zcash.Snark.ZeroKnowledge.CommitmentEntryCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost
import Zcash.Snark.ZeroKnowledge.PolynomialCommitment

/-!
# Counted private opening-group commitments

The group fold constructs the actual member identifiers, routes every emitted
commitment, and applies the original Horner weights. All selected point-reader
costs and all group operations remain in the counter.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Reconstruct a private opening commitment with its complete member-routing costs. -/
def privateOpeningPointCosted (groupAdd groupScale equal : ℕ) {actions : ℕ}
    (points : Fin (22 * actions + 10) → G × ℕ) (challenge : Fp × ℕ) (group : Fin 4) : G × ℕ :=
  let members := privateOpeningGroupCosted actions group
  let value := foldlCosted (fun state id =>
    let point := plonkColumnEntryCosted equal points id
    (challenge.1 • state + point.1, challenge.2 + point.2 + groupScale + groupAdd + 1))
    members.1 (0, 1)
  (value.1, members.2 + value.2 + 1)

/-- Erasure is the original commitment fold over precisely the original private members. -/
theorem privateOpeningPointCosted_result (groupAdd groupScale equal : ℕ) {actions : ℕ}
    (points : Fin (22 * actions + 10) → G × ℕ) (challenge : Fp × ℕ) (group : Fin 4) :
    (privateOpeningPointCosted groupAdd groupScale equal points challenge group).1 =
      commitmentHornerFold challenge.1 ((plonkPrivateGroupMembers actions group).map
        (plonkColumnEntry (fun index => (points index).1))) := by
  simp only [privateOpeningPointCosted, foldlCosted_result, privateOpeningGroupCosted_result,
    plonkColumnEntryCosted_result, commitmentHornerFold, List.foldl_map]

/-- The full bound includes group construction, complete entry routing, and all Horner operations. -/
theorem privateOpeningPointCosted_cost_le (groupAdd groupScale equal : ℕ) {actions : ℕ}
    (points : Fin (22 * actions + 10) → G × ℕ) (challenge : Fp × ℕ) (group : Fin 4)
    (access : ℕ) (hread : ∀ index, (points index).2 ≤ access) :
    (privateOpeningPointCosted groupAdd groupScale equal points challenge group).2 ≤
      actions * actions + 35 * actions + 9 * actions *
        (4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + access + 13 +
          challenge.2 + groupScale + groupAdd + 2) + 4 := by
  let members := privateOpeningGroupCosted actions group
  let routeBudget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + access + 13
  let step := fun (state : G) (id : PrivateColumnId actions) =>
    (challenge.1 • state + (plonkColumnEntryCosted equal points id).1,
      challenge.2 + (plonkColumnEntryCosted equal points id).2 + groupScale + groupAdd + 1)
  let stepBudget := challenge.2 + routeBudget + groupScale + groupAdd + 1
  have hstep (state : G) (id : PrivateColumnId actions) : (step state id).2 ≤ stepBudget := by
    have h := plonkColumnEntryCosted_cost_le equal points id access hread
    dsimp only [step, stepBudget, routeBudget]
    omega
  have hfold := foldlCosted_cost_le_sum step members.1 (0, 1) (fun _ => True) (fun _ => stepBudget)
    trivial (fun _ _ _ _ => trivial) (fun state _ id _ => hstep state id)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hfold
  have hmembers := privateOpeningGroupCosted_cost_le actions group
  have hlength := privateOpeningGroupCosted_length_le actions group
  have hscaled := Nat.mul_le_mul_right (stepBudget + 1) hlength
  change members.2 + (foldlCosted step members.1 (0, 1)).2 + 1 ≤ _
  dsimp only [stepBudget, routeBudget] at *
  nlinarith

end Zcash.Snark.ZeroKnowledge
