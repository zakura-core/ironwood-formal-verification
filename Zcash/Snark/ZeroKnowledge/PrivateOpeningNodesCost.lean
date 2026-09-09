import Zcash.Snark.ZeroKnowledge.PrivateOpeningEvaluationCost
import Zcash.Snark.ZeroKnowledge.PlonkMultiopen

/-!
# Counted private opening-node lists

Each group's node-index list is the original fixed order. The counted algorithm
constructs that list and performs the complete routed private-group evaluation
at every selected node, retaining every scalar-reader and arithmetic cost.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Construct a group's original node indices, counting branch selection and each literal/list cell. -/
def openingPointIndicesCosted (group : Fin 5) : List (Fin 5) × ℕ :=
  let indices : List (Fin 5) := match group.val with
    | 0 => [0]
    | 1 => [0, 1]
    | 2 => [0, 1, 2]
    | 3 => [0, 1, 3]
    | _ => [0, 2]
  (indices, 16)

/-- Every node index and its order agree with the original multi-opening definition. -/
theorem openingPointIndicesCosted_result (group : Fin 5) :
    (openingPointIndicesCosted group).1 = plonkOpeningPointIndices group := by
  fin_cases group <;> rfl

/-- All groups contain between one and three materialized node indices. -/
theorem openingPointIndicesCosted_length (group : Fin 5) :
    0 < (openingPointIndicesCosted group).1.length ∧ (openingPointIndicesCosted group).1.length ≤ 3 := by
  fin_cases group <;> decide

/-- The fixed-table construction retains an explicit structural cost. -/
theorem openingPointIndicesCosted_cost (group : Fin 5) : (openingPointIndicesCosted group).2 = 16 := rfl

/-- Compute every node value for one complete private opening group. -/
def privateOpeningNodesCosted (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (challenge : Fp × ℕ) (group : Fin 4) : List Fp × ℕ :=
  let indices := openingPointIndicesCosted group.succ
  let values := mapListCosted
    (privateOpeningEvaluationCosted (actions := actions) costs equal read views challenge group) indices.1
  (values.1, indices.2 + values.2 + 1)

/-- The materialized node values are the exact original private-group scalar folds. -/
theorem privateOpeningNodesCosted_result (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (challenge : Fp × ℕ) (group : Fin 4) :
    (privateOpeningNodesCosted (actions := actions) costs equal read views challenge group).1 =
      (plonkOpeningPointIndices group.succ).map fun point =>
        plonkScalarFold challenge.1 ((plonkPrivateGroupMembers actions group).map fun id =>
          privateColumnView (views.map (fun column index => (column index).1)) id point) := by
  simp only [privateOpeningNodesCosted, mapListCosted_result, openingPointIndicesCosted_result,
    privateOpeningEvaluationCosted_result]

/-- The node list is completely materialized and preserves the original node count. -/
theorem privateOpeningNodesCosted_length (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (challenge : Fp × ℕ) (group : Fin 4) :
    (privateOpeningNodesCosted (actions := actions) costs equal read views challenge group).1.length =
      (plonkOpeningPointIndices group.succ).length := by
  rw [privateOpeningNodesCosted_result, List.length_map]

/-- Every node evaluation includes complete member construction, routing, and Horner work. -/
theorem privateOpeningNodesCosted_cost_le (costs : FieldOperationCosts) (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (challenge : Fp × ℕ) (group : Fin 4)
    (access : ℕ) (hread : ∀ column ∈ views, ∀ index, (column index).2 ≤ access) :
    (privateOpeningNodesCosted (actions := actions) costs equal read views challenge group).2 ≤
      3 * (privateOpeningEvaluationCostBudget costs equal read actions views.length access challenge.2 + 1) + 18 := by
  have hmap := mapListCosted_cost_le
    (privateOpeningEvaluationCosted (actions := actions) costs equal read views challenge group)
    (openingPointIndicesCosted group.succ).1
    (privateOpeningEvaluationCostBudget costs equal read actions views.length access challenge.2)
    (fun point _ => privateOpeningEvaluationCosted_cost_le costs equal read views challenge group point access hread)
  have hlength := (openingPointIndicesCosted_length group.succ).2
  have hscaled := Nat.mul_le_mul_right
    (privateOpeningEvaluationCostBudget costs equal read actions views.length access challenge.2 + 1) hlength
  simp only [privateOpeningNodesCosted, openingPointIndicesCosted_cost]
  omega

end Zcash.Snark.ZeroKnowledge
