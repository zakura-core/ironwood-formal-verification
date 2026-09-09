import Zcash.Snark.ZeroKnowledge.PlonkColumns
import Zcash.Snark.ZeroKnowledge.ListCollectedCost

/-!
# Counted construction of the actual private-column order

The four phases retain the original Action and column nesting. Every identifier,
list cell, finite-index adapter, and append traversal is included in the count.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- A finite collection of equally sized materialized lists has the exact total length. -/
theorem flattenFinCosted_length_eq {α : Type*} {count : ℕ}
    (read : Fin count → List α × ℕ) (length : ℕ)
    (hlength : ∀ index, (read index).1.length = length) :
    (flattenFinCosted read).1.length = count * length := by
  rw [flattenFinCosted_result, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, hlength, List.ofFn_const, List.sum_replicate, smul_eq_mul]

/-- Construct the original four private-column phases with all structural work counted. -/
def privateColumnOrderCosted (actions : ℕ) : List (PrivateColumnId actions) × ℕ :=
  let advice := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 10 => (PrivateColumnId.advice action column, 1)
  let lookups := flattenFinCosted fun action : Fin actions =>
    flattenFinCosted fun lookup : Fin 3 =>
      ([PrivateColumnId.lookupInput action lookup, .lookupTable action lookup], 3)
  let permutations := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 3 => (PrivateColumnId.permutationProduct action column, 1)
  let products := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 3 => (PrivateColumnId.lookupProduct action column, 1)
  let first := appendListCosted advice.1 lookups.1
  let second := appendListCosted first.1 permutations.1
  let result := appendListCosted second.1 products.1
  (result.1, advice.2 + lookups.2 + permutations.2 + products.2 + first.2 + second.2 + result.2 + 1)

/-- Erasure preserves every original identifier and its exact position. -/
theorem privateColumnOrderCosted_result (actions : ℕ) :
    (privateColumnOrderCosted actions).1 = privateColumnOrder actions := by
  simp only [privateColumnOrderCosted, appendListCosted_result, flattenFinCosted_result,
    ofFnCosted_result, privateColumnOrder, List.flatMap, List.ofFn_eq_map]

/-- The materialized schedule has exactly twenty-two identifiers per Action. -/
theorem privateColumnOrderCosted_length (actions : ℕ) :
    (privateColumnOrderCosted actions).1.length = 22 * actions := by
  rw [privateColumnOrderCosted_result, privateColumnOrder_length]

/-- Complete construction cost for the pinned schedule, including all three append traversals. -/
theorem privateColumnOrderCosted_cost_le (actions : ℕ) :
    (privateColumnOrderCosted actions).2 ≤ 4 * actions * actions + 260 * actions + 10 := by
  let advice := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 10 => (PrivateColumnId.advice action column, 1)
  let lookups := flattenFinCosted fun action : Fin actions =>
    flattenFinCosted fun lookup : Fin 3 =>
      ([PrivateColumnId.lookupInput action lookup, .lookupTable action lookup], 3)
  let permutations := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 3 => (PrivateColumnId.permutationProduct action column, 1)
  let products := flattenFinCosted fun action : Fin actions =>
    ofFnCosted fun column : Fin 3 => (PrivateColumnId.lookupProduct action column, 1)
  have hAdvice : advice.2 ≤ actions * 133 + actions * actions + 1 := by
    apply flattenFinCosted_cost_le (budget := 121) (length := 10)
    · intro action
      exact ofFnCosted_cost_le (fun column : Fin 10 => (PrivateColumnId.advice action column, 1)) 1 (by simp)
    · intro action
      exact (ofFnCosted_length (fun column : Fin 10 => (PrivateColumnId.advice action column, 1))).le
  have hLookups : lookups.2 ≤ actions * 39 + actions * actions + 1 := by
    apply flattenFinCosted_cost_le (budget := 31) (length := 6)
    · intro action
      exact flattenFinCosted_cost_le (fun lookup : Fin 3 =>
        ([PrivateColumnId.lookupInput action lookup, .lookupTable action lookup], 3)) 3 2
        (by simp) (by simp)
    · intro action
      exact (flattenFinCosted_length_eq (fun lookup : Fin 3 =>
        ([PrivateColumnId.lookupInput action lookup, .lookupTable action lookup], 3)) 2 (by simp)).le
  have hPermutations : permutations.2 ≤ actions * 21 + actions * actions + 1 := by
    apply flattenFinCosted_cost_le (budget := 16) (length := 3)
    · intro action
      exact ofFnCosted_cost_le (fun column : Fin 3 => (PrivateColumnId.permutationProduct action column, 1)) 1 (by simp)
    · intro action
      exact (ofFnCosted_length (fun column : Fin 3 => (PrivateColumnId.permutationProduct action column, 1))).le
  have hProducts : products.2 ≤ actions * 21 + actions * actions + 1 := by
    apply flattenFinCosted_cost_le (budget := 16) (length := 3)
    · intro action
      exact ofFnCosted_cost_le (fun column : Fin 3 => (PrivateColumnId.lookupProduct action column, 1)) 1 (by simp)
    · intro action
      exact (ofFnCosted_length (fun column : Fin 3 => (PrivateColumnId.lookupProduct action column, 1))).le
  have hAdviceLength : advice.1.length = actions * 10 :=
    flattenFinCosted_length_eq _ 10 (fun _ => ofFnCosted_length _)
  have hLookupLength : lookups.1.length = actions * 6 :=
    flattenFinCosted_length_eq _ 6 (fun action =>
      flattenFinCosted_length_eq (fun lookup : Fin 3 =>
        ([PrivateColumnId.lookupInput action lookup, .lookupTable action lookup], 3)) 2 (by simp))
  have hPermutationLength : permutations.1.length = actions * 3 :=
    flattenFinCosted_length_eq _ 3 (fun _ => ofFnCosted_length _)
  change advice.2 + lookups.2 + permutations.2 + products.2 +
    (appendListCosted advice.1 lookups.1).2 +
    (appendListCosted (appendListCosted advice.1 lookups.1).1 permutations.1).2 +
    (appendListCosted (appendListCosted (appendListCosted advice.1 lookups.1).1 permutations.1).1 products.1).2 + 1 ≤ _
  simp only [appendListCosted_cost, appendListCosted_result, List.length_append,
    hAdviceLength, hLookupLength, hPermutationLength]
  nlinarith

end Zcash.Snark.ZeroKnowledge
