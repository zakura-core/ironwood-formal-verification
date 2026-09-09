import Zcash.Snark.ZeroKnowledge.MultiopenEvaluationCost
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

/-!
# Counted assembly of materialized multi-opening inputs

The five entries are read from already constructed point, node-value, and group-
value vectors. Their preparation costs are retained once, and every subsequent
list access is counted. No list entry contains a deferred scalar computation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Read and assemble one point-set entry, paying for all three list traversals. -/
def openingSetEntryCosted (read : ℕ) (points nodes : List (List Fp)) (values : List Fp)
    (index : Fin 5) : (List Fp × List Fp × (Fp × ℕ)) × ℕ :=
  let pointSet := getDListCosted read [] points index.val
  let nodeValues := getDListCosted read [] nodes index.val
  let value := getDListCosted read 0 values index.val
  ((pointSet.1, nodeValues.1, (value.1, 1)), pointSet.2 + nodeValues.2 + value.2 + 4)

/-- The entry preserves the original list defaults and records a materialized scalar read. -/
theorem openingSetEntryCosted_result (read : ℕ) (points nodes : List (List Fp)) (values : List Fp)
    (index : Fin 5) :
    (openingSetEntryCosted read points nodes values index).1 =
      (points.getD index.val [], nodes.getD index.val [], (values.getD index.val 0, 1)) := by
  simp only [openingSetEntryCosted, getDListCosted_result]

/-- Materialized finite vectors supply exactly their indexed entries. -/
theorem openingSetEntryCosted_ofFn (read : ℕ) (points nodes : Fin 5 → List Fp)
    (values : Fin 5 → Fp) (index : Fin 5) :
    (openingSetEntryCosted read (List.ofFn points) (List.ofFn nodes) (List.ofFn values) index).1 =
      (points index, nodes index, (values index, 1)) := by
  have hp : index.val < (List.ofFn points).length := by simpa only [List.length_ofFn] using index.isLt
  have hn : index.val < (List.ofFn nodes).length := by simpa only [List.length_ofFn] using index.isLt
  have hv : index.val < (List.ofFn values).length := by simpa only [List.length_ofFn] using index.isLt
  simp only [openingSetEntryCosted_result, List.getD_eq_getElem _ _ hp,
    List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ hv, List.getElem_ofFn]

/-- The entry bound includes each actual list length and scalar or list-head access. -/
theorem openingSetEntryCosted_cost_le (read : ℕ) (points nodes : List (List Fp)) (values : List Fp)
    (index : Fin 5) :
    (openingSetEntryCosted read points nodes values index).2 ≤
      2 * (points.length + nodes.length + values.length) + 3 * read + 7 := by
  have hp := getDListCosted_cost_le read [] points index.val
  have hn := getDListCosted_cost_le read [] nodes index.val
  have hv := getDListCosted_cost_le read 0 values index.val
  simp only [openingSetEntryCosted]
  omega

/-- Assemble all five entries and retain the complete preparation of all three input vectors. -/
def openingEvaluationSetsCosted (read : ℕ) (points nodes : List (List Fp) × ℕ)
    (values : List Fp × ℕ) : List (List Fp × List Fp × (Fp × ℕ)) × ℕ :=
  let entries := ofFnCosted (openingSetEntryCosted read points.1 nodes.1 values.1)
  (entries.1, points.2 + nodes.2 + values.2 + entries.2 + 1)

/-- Complete finite input vectors assemble into exactly the reference five-group order. -/
theorem openingEvaluationSetsCosted_result (read : ℕ) (points nodes : Fin 5 → List Fp)
    (values : Fin 5 → Fp) (pointCost nodeCost valueCost : ℕ) :
    (openingEvaluationSetsCosted read (List.ofFn points, pointCost)
      (List.ofFn nodes, nodeCost) (List.ofFn values, valueCost)).1 =
      List.ofFn (fun index => (points index, nodes index, (values index, 1))) := by
  simp only [openingEvaluationSetsCosted, ofFnCosted_result, openingSetEntryCosted_ofFn]

/-- Assembly always materializes five entries, including the default cases. -/
theorem openingEvaluationSetsCosted_length (read : ℕ) (points nodes : List (List Fp) × ℕ)
    (values : List Fp × ℕ) :
    (openingEvaluationSetsCosted read points nodes values).1.length = 5 := ofFnCosted_length _

/-- Preparation, all indexed reads, and all output cells remain in the total assembly budget. -/
theorem openingEvaluationSetsCosted_cost_le (read : ℕ) (points nodes : List (List Fp) × ℕ)
    (values : List Fp × ℕ) :
    (openingEvaluationSetsCosted read points nodes values).2 ≤
      points.2 + nodes.2 + values.2 +
        5 * (2 * (points.1.length + nodes.1.length + values.1.length) + 3 * read + 8) + 27 := by
  have hentries := ofFnCosted_cost_le (openingSetEntryCosted read points.1 nodes.1 values.1)
    _ (openingSetEntryCosted_cost_le read points.1 nodes.1 values.1)
  simp only [openingEvaluationSetsCosted]
  omega

/-- A concrete five-group evaluator budget follows from the actual at-most-three-node sizes. -/
theorem multiopenEvalCostBudget_le_five (costs : FieldOperationCosts) (read x2Access x3Access claimAccess : ℕ)
    (sets : List (List Fp × List Fp × (Fp × ℕ))) (hlength : sets.length ≤ 5)
    (hsets : ∀ entry ∈ sets, entry.1.length ≤ 3 ∧ entry.2.1.length ≤ 3 ∧ entry.2.2.2 ≤ claimAccess) :
    multiopenEvalCostBudget costs read x2Access x3Access sets ≤
      5 * (multiopenSetEvalCostBudget costs read 3 3 x3Access claimAccess +
        x2Access + costs.multiply + costs.add + 4) + 7 := by
  let budget := multiopenSetEvalCostBudget costs read 3 3 x3Access claimAccess +
    x2Access + costs.multiply + costs.add + 4
  have hentry (entry) (hmem : entry ∈ sets) :
      multiopenSetEvalCostBudget costs read entry.1.length entry.2.1.length x3Access entry.2.2.2 +
        x2Access + costs.multiply + costs.add + 4 ≤ budget := by
    obtain ⟨hp, hn, hv⟩ := hsets entry hmem
    dsimp only [budget]
    unfold multiopenSetEvalCostBudget lagrangeEvalCostBudget interpolationWeightCostBudget
    gcongr
  have hsum := List.sum_le_sum hentry
  have hsum' : (sets.map (fun entry =>
      multiopenSetEvalCostBudget costs read entry.1.length entry.2.1.length x3Access entry.2.2.2 +
        x2Access + costs.multiply + costs.add + 4)).sum ≤ sets.length * budget := by
    simpa only [List.map_const', List.sum_replicate, smul_eq_mul] using hsum
  have hscaled := Nat.mul_le_mul_right budget hlength
  unfold multiopenEvalCostBudget
  dsimp only [budget] at hsum' hscaled
  omega

end Zcash.Snark.ZeroKnowledge
