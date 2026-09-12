import Zcash.Snark.ZeroKnowledge.PrivateColumnOrderCost
import Zcash.Snark.ZeroKnowledge.PlonkTape

namespace Zcash.Snark.ZeroKnowledge

/-- Materialize the source's four phases of private-column batches, including all nesting and copies. -/
def privateColumnBatchesCosted (actions : ℕ) : List (List (PrivateColumnId actions)) × ℕ :=
  let advice := ofFnCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 10 => (PrivateColumnId.advice action column, 1)
  let lookups := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun lookup : Fin 3 =>
      ([PrivateColumnId.lookupInput action lookup, .lookupTable action lookup], 3)
  let permutations := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 3 => ([PrivateColumnId.permutationProduct action column], 2)
  let products := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 3 => ([PrivateColumnId.lookupProduct action column], 2)
  let first := appendListCosted advice.1 lookups.1
  let second := appendListCosted first.1 permutations.1
  let result := appendListCosted second.1 products.1
  (result.1, advice.2 + lookups.2 + permutations.2 + products.2 + first.2 + second.2 + result.2 + 1)

/-- The counted batch list is the existing source list with the exact original boundaries. -/
theorem privateColumnBatchesCosted_result (actions : ℕ) :
    (privateColumnBatchesCosted actions).1 = privateColumnBatches actions := by
  simp only [privateColumnBatchesCosted, appendListCosted_result, flattenFinCosted_result,
    ofFnCosted_result, privateColumnBatches, List.flatMap, List.ofFn_eq_map]

/-- There are ten source batches for each Action. -/
theorem privateColumnBatches_length (actions : ℕ) : (privateColumnBatches actions).length = 10 * actions := by
  simp [privateColumnBatches, List.length_flatMap, Nat.mul_comm]
  omega

/-- Batch preparation is bounded independently of sampled values and prover callbacks. -/
theorem privateColumnBatchesCosted_cost_le (actions : ℕ) :
    (privateColumnBatchesCosted actions).2 ≤ 4 * actions * actions + 260 * actions + 10 := by
  let advice := ofFnCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 10 => (PrivateColumnId.advice action column, 1)
  let lookups := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun lookup : Fin 3 =>
      ([PrivateColumnId.lookupInput action lookup, .lookupTable action lookup], 3)
  let permutations := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 3 => ([PrivateColumnId.permutationProduct action column], 2)
  let products := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 3 => ([PrivateColumnId.lookupProduct action column], 2)
  have ha : advice.2 ≤ actions * 122 + actions * actions + 1 :=
    ofFnCosted_cost_le _ 121 (fun action => ofFnCosted_cost_le _ 1 (by simp))
  have hl : lookups.2 ≤ actions * 27 + actions * actions + 1 :=
    flattenFinCosted_cost_le _ 22 3 (fun action => ofFnCosted_cost_le _ 3 (by simp))
      (fun action => (ofFnCosted_length _).le)
  have hp : permutations.2 ≤ actions * 24 + actions * actions + 1 :=
    flattenFinCosted_cost_le _ 19 3 (fun action => ofFnCosted_cost_le _ 2 (by simp))
      (fun action => (ofFnCosted_length _).le)
  have hz : products.2 ≤ actions * 24 + actions * actions + 1 :=
    flattenFinCosted_cost_le _ 19 3 (fun action => ofFnCosted_cost_le _ 2 (by simp))
      (fun action => (ofFnCosted_length _).le)
  have hna : advice.1.length = actions := ofFnCosted_length _
  have hnl : lookups.1.length = actions * 3 := flattenFinCosted_length_eq _ 3 (fun _ => ofFnCosted_length _)
  have hnp : permutations.1.length = actions * 3 := flattenFinCosted_length_eq _ 3 (fun _ => ofFnCosted_length _)
  change advice.2 + lookups.2 + permutations.2 + products.2 +
    (appendListCosted advice.1 lookups.1).2 +
    (appendListCosted (appendListCosted advice.1 lookups.1).1 permutations.1).2 +
    (appendListCosted (appendListCosted (appendListCosted advice.1 lookups.1).1 permutations.1).1 products.1).2 + 1 ≤ _
  simp only [appendListCosted_cost, appendListCosted_result, List.length_append, hna, hnl, hnp]
  nlinarith

end Zcash.Snark.ZeroKnowledge
