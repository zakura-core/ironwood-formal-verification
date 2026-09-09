import Zcash.Snark.ZeroKnowledge.PublicOpeningValueCost
import Zcash.Snark.ZeroKnowledge.PrivateOpeningNodesCost

/-!
# Counted opening-node and group-value vectors

Both scalar vectors are fully materialized. Node values include the complete
public row-polynomial preparation and every routed private-group fold. Group
values retain the simulator's first scalar and compute all four private folds
at the final observation point. No supplied scalar producer is treated as free.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Construct every original opening-node list in group order. -/
def openingNodeValuesCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x x1 hEval rEval : Fp × ℕ) : List (List Fp) × ℕ :=
  let first := firstPublicOpeningValueCosted costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval
  let rest := ofFnCosted (privateOpeningNodesCosted (actions := actions) costs equal read views x1)
  ([first.1] :: rest.1, first.2 + rest.2 + 3)

/-- All five materialized node lists agree with the reference public reconstruction. -/
theorem openingNodeValuesCosted_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x x1 hEval rEval : Fp × ℕ)
    {G : Type*} (points : Fin (22 * actions + 10) → G) (firstGroup : Fp) :
    (openingNodeValuesCosted costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval).1 =
      List.ofFn (plonkPublicNodeValues
        (plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
          (fun column row => (fixed column row).1) (fun column row => (sigma column row).1))
        x.1 x1.1 hEval.1 (points, views.map (fun column index => (column index).1), rEval.1, firstGroup)) := by
  conv_rhs => rw [List.ofFn_succ]
  simp only [openingNodeValuesCosted, ofFnCosted_result, firstPublicOpeningValueCosted_result,
    plonkPublicNodeValues, Fin.cons_zero, Fin.cons_succ, privateOpeningNodesCosted_result]

/-- There are exactly five materialized node lists. -/
theorem openingNodeValuesCosted_length (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x x1 hEval rEval : Fp × ℕ) :
    (openingNodeValuesCosted costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval).1.length = 5 := by
  simp only [openingNodeValuesCosted, List.length_cons, ofFnCosted_length]

/-- Every fully constructed node list contains between one and three scalars. -/
theorem openingNodeValuesCosted_node_lengths (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (x x1 hEval rEval : Fp × ℕ)
    (nodes : List Fp)
    (hnodes : nodes ∈ (openingNodeValuesCosted costs equal read omegaAccess
      instances fixed sigma views x x1 hEval rEval).1) :
    0 < nodes.length ∧ nodes.length ≤ 3 := by
  simp only [openingNodeValuesCosted, List.mem_cons, ofFnCosted_result, List.mem_ofFn] at hnodes
  rcases hnodes with rfl | ⟨group, rfl⟩
  · change 0 < 1 ∧ (1 : ℕ) ≤ 3
    decide
  · rw [privateOpeningNodesCosted_length]
    simpa only [openingPointIndicesCosted_result] using openingPointIndicesCosted_length group.succ

/-- This total includes the full first-group preparation and every private node calculation. -/
theorem openingNodeValuesCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
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
    let firstBudget := actions * actions + actions * (4 * access + 40) + 50 * access + 1200 +
      (4 * actions + 46) * (x1.2 + costs.multiply + costs.add + 3) + 3
    let privateBudget := 3 *
      (privateOpeningEvaluationCostBudget costs equal read actions views.length observationRead x1.2 + 1) + 18
    (openingNodeValuesCosted costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval).2 ≤
      firstBudget + 4 * (privateBudget + 1) + 20 := by
  have hfirst := firstPublicOpeningValueCosted_cost_le costs equal read omegaAccess
    instances fixed sigma views x x1 hEval rEval rowRead observationRead hinstances hfixed hsigma hviews
  have hrest := ofFnCosted_cost_le (privateOpeningNodesCosted (actions := actions) costs equal read views x1)
    _ (fun group => privateOpeningNodesCosted_cost_le costs equal read views x1 group observationRead hviews)
  dsimp only
  simp only [openingNodeValuesCosted]
  omega

/-- Materialize all five group values, computing the four original private folds at point four. -/
def openingGroupValuesCosted (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (x1 firstGroup : Fp × ℕ) : List Fp × ℕ :=
  let rest := ofFnCosted (fun group =>
    privateOpeningEvaluationCosted (actions := actions) costs equal read views x1 group 4)
  (firstGroup.1 :: rest.1, firstGroup.2 + rest.2 + 2)

/-- The materialized group values equal the reference pre-IPA projection. -/
theorem openingGroupValuesCosted_result (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (x1 firstGroup : Fp × ℕ)
    {G : Type*} (pub : PlonkPublicPolynomials actions) (x rEval : Fp)
    (points : Fin (22 * actions + 10) → G) :
    (openingGroupValuesCosted (actions := actions) costs equal read views x1 firstGroup).1 =
      List.ofFn (plonkPreIpaProjection pub x x1.1
        (points, views.map (fun column index => (column index).1), rEval, firstGroup.1)).groupValues := by
  conv_rhs => rw [List.ofFn_succ]
  simp only [openingGroupValuesCosted, ofFnCosted_result, privateOpeningEvaluationCosted_groupValue,
    plonkPreIpaProjection, Fin.cons_zero, Fin.cons_succ]

/-- All five group scalars are materialized before multi-opening. -/
theorem openingGroupValuesCosted_length (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (x1 firstGroup : Fp × ℕ) :
    (openingGroupValuesCosted (actions := actions) costs equal read views x1 firstGroup).1.length = 5 := by
  simp only [openingGroupValuesCosted, List.length_cons, ofFnCosted_length]

/-- The first supplied scalar and every complete private fold remain in the group-vector budget. -/
theorem openingGroupValuesCosted_cost_le (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (x1 firstGroup : Fp × ℕ)
    (observationRead : ℕ) (hviews : ∀ column ∈ views, ∀ index, (column index).2 ≤ observationRead) :
    (openingGroupValuesCosted (actions := actions) costs equal read views x1 firstGroup).2 ≤
      firstGroup.2 + 4 *
        (privateOpeningEvaluationCostBudget costs equal read actions views.length observationRead x1.2 + 1) + 19 := by
  have hrest := ofFnCosted_cost_le (fun group =>
    privateOpeningEvaluationCosted (actions := actions) costs equal read views x1 group 4)
    _ (fun group => privateOpeningEvaluationCosted_cost_le costs equal read views x1 group 4 observationRead hviews)
  simp only [openingGroupValuesCosted]
  omega

end Zcash.Snark.ZeroKnowledge
