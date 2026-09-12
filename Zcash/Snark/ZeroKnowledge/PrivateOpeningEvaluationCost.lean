import Zcash.Snark.ZeroKnowledge.OpeningGroupLayoutCost
import Zcash.Snark.ZeroKnowledge.PrivateColumnRoutingCost
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost

/-!
# Counted private opening-group evaluation

Construct the actual member identifiers and route each disclosed column value
inside the original Horner fold. The bound includes identifier construction,
private-column ordering and search, every selected reader, and all arithmetic.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Evaluate a private group's disclosed values with all layout and routing costs retained. -/
def privateOpeningEvaluationCosted (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (challenge : Fp × ℕ) (group : Fin 4) (point : Fin 5) : Fp × ℕ :=
  let members := privateOpeningGroupCosted actions group
  let value := foldlCosted (fun state id =>
    let disclosed := privateColumnViewCosted equal read views id point
    (state * challenge.1 + disclosed.1,
      challenge.2 + disclosed.2 + costs.multiply + costs.add + 1)) members.1 (0, 1)
  (value.1, members.2 + value.2 + 1)

/-- Erasure preserves the original private-group order and the selected disclosed point. -/
theorem privateOpeningEvaluationCosted_result (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (challenge : Fp × ℕ) (group : Fin 4) (point : Fin 5) :
    (privateOpeningEvaluationCosted (actions := actions) costs equal read views challenge group point).1 =
      plonkScalarFold challenge.1 ((plonkPrivateGroupMembers actions group).map fun id =>
        privateColumnView (views.map (fun column index => (column index).1)) id point) := by
  simp only [privateOpeningEvaluationCosted, foldlCosted_result, privateOpeningGroupCosted_result,
    privateColumnViewCosted_result, plonkScalarFold, List.foldl_map]

/-- Point four is exactly the subsequent quotient-opening claim used by the pre-IPA projection. -/
theorem privateOpeningEvaluationCosted_groupValue (costs : FieldOperationCosts) (equal read : ℕ)
    {actions : ℕ} (views : List (Fin 5 → Fp × ℕ)) (challenge : Fp × ℕ) (group : Fin 4) :
    (privateOpeningEvaluationCosted (actions := actions) costs equal read views challenge group 4).1 =
      plonkPrivateGroupValues (actions := actions) challenge.1
        (views.map (fun column index => (column index).1)) group :=
  privateOpeningEvaluationCosted_result (actions := actions) costs equal read views challenge group 4

/-- Explicit bound for layout, complete column routing, and the final Horner fold. -/
def privateOpeningEvaluationCostBudget (costs : FieldOperationCosts)
    (equal read actions columns access challengeAccess : ℕ) : ℕ :=
  actions * actions + 35 * actions + 9 * actions *
    (4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
      2 * columns + read + access + 15 + challengeAccess + costs.multiply + costs.add + 2) + 4

/-- Every private-group evaluation fits the bound, even for missing columns and exceptional fields. -/
theorem privateOpeningEvaluationCosted_cost_le (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (challenge : Fp × ℕ) (group : Fin 4) (point : Fin 5)
    (access : ℕ) (hread : ∀ column ∈ views, ∀ index, (column index).2 ≤ access) :
    (privateOpeningEvaluationCosted (actions := actions) costs equal read views challenge group point).2 ≤
      privateOpeningEvaluationCostBudget costs equal read actions views.length access challenge.2 := by
  let members := privateOpeningGroupCosted actions group
  let routeBudget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
    2 * views.length + read + access + 15
  let step := fun (state : Fp) (id : PrivateColumnId actions) =>
    (state * challenge.1 + (privateColumnViewCosted equal read views id point).1,
      challenge.2 + (privateColumnViewCosted equal read views id point).2 + costs.multiply + costs.add + 1)
  let stepBudget := challenge.2 + routeBudget + costs.multiply + costs.add + 1
  have hstep (state : Fp) (id : PrivateColumnId actions) : (step state id).2 ≤ stepBudget := by
    have h := privateColumnViewCosted_cost_le equal read views id point access hread
    dsimp only [step, stepBudget, routeBudget]
    omega
  have hfold := foldlCosted_cost_le_sum step members.1 (0, 1) (fun _ => True) (fun _ => stepBudget)
    trivial (fun _ _ _ _ => trivial) (fun state _ id _ => hstep state id)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hfold
  have hmembers := privateOpeningGroupCosted_cost_le actions group
  have hlength := privateOpeningGroupCosted_length_le actions group
  have hscaled := Nat.mul_le_mul_right (stepBudget + 1) hlength
  change members.2 + (foldlCosted step members.1 (0, 1)).2 + 1 ≤ _
  dsimp only [privateOpeningEvaluationCostBudget, stepBudget, routeBudget] at *
  nlinarith

end Zcash.Snark.ZeroKnowledge
