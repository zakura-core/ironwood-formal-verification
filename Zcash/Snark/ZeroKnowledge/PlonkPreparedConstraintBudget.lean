import Zcash.Snark.ZeroKnowledge.PlonkClaimInputBounds

/-!
# Constraint budget from actual key and claim sizes

Three permutation records and three lookup records are constructed by the
original claim preparation. Their bounds below are derived from those lists;
the key's actual gate trees, column layout, and lookup trees determine the
remaining sizes.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- A polynomial budget using the actual key trees and its complete column layout. -/
def plonkPreparedConstraintCostBudget (costs : FieldOperationCosts) (node access : ℕ)
    (gates : List (Expr Fp)) (layout : List (List (ColumnRef × ℕ)))
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) (stride : ℕ) : ℕ :=
  let lookupNodes := (List.ofFn (fun index => ((inputs index).1.map exprNodeCount).sum +
    ((tables index).1.map exprNodeCount).sum)).sum
  let lookupWidth := (List.ofFn (fun index => (inputs index).1.length + (tables index).1.length)).sum
  let lookupBudget := 2 * (lookupNodes * (node + 1 + access + costs.add + costs.negate + costs.multiply) +
    lookupWidth * (access + costs.multiply + costs.add + 2) + 2) +
    50 * access + 100 * (costs.add + costs.negate + costs.multiply + 1)
  gates.length * ((gates.map exprNodeCount).sum *
    (node + 1 + access + costs.add + costs.negate + costs.multiply) + 1) + 1 +
    (3 * (3 * access + costs.add + costs.negate + costs.multiply + 12) +
      3 * (permutationChunkListCostBudget costs access (3 * (layout.map List.length).sum) 3 stride + 2) +
      20 * access + 30 * (costs.add + costs.negate + costs.multiply + 1)) +
    (3 * (lookupBudget + 7) + 1) + 2 * gates.length + 3 + 3 + 5

/-- The generic evaluator's complete budget follows from the actual prepared claim lists. -/
theorem plonkPreparedConstraintCostBudget_bound (costs : FieldOperationCosts) (node access equal read : ℕ)
    {actions : ℕ} (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (gates : List (Expr Fp)) (layout : List (List (ColumnRef × ℕ)) × ℕ)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) (stride : ℕ) :
    subProofConstraintCostBudget costs node access gates
      (plonkPermutationSetsCosted equal read views action).1
      (permutationQueryChunksCosted instanceRead advice fixed sigma
        (plonkPermutationSetsCosted equal read views action) layout).1
      (plonkLookupInputsCosted equal read views action inputs tables).1 stride ≤
        plonkPreparedConstraintCostBudget costs node access gates layout.1 inputs tables stride := by
  have hlength := permutationQueryChunksCosted_length_le instanceRead advice fixed sigma
    (plonkPermutationSetsCosted equal read views action) layout
  have hcolumns := permutationQueryChunksCosted_columns_le instanceRead advice fixed sigma
    (plonkPermutationSetsCosted equal read views action) layout
  rw [plonkPermutationSetsCosted_length] at hlength hcolumns
  have hpermutation : subProofPermutationCostBudget costs access
      (plonkPermutationSetsCosted equal read views action).1
      (permutationQueryChunksCosted instanceRead advice fixed sigma
        (plonkPermutationSetsCosted equal read views action) layout).1 stride ≤
      3 * (3 * access + costs.add + costs.negate + costs.multiply + 12) +
        3 * (permutationChunkListCostBudget costs access (3 * (layout.1.map List.length).sum) 3 stride + 2) +
        20 * access + 30 * (costs.add + costs.negate + costs.multiply + 1) := by
    simp only [subProofPermutationCostBudget, plonkPermutationSetsCosted_length]
    apply Nat.add_le_add_right
    apply Nat.add_le_add_right
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul hlength
    apply Nat.add_le_add_right
    unfold permutationChunkListCostBudget
    gcongr
  have hlookup : subProofLookupCostBudget costs node access
      (plonkLookupInputsCosted equal read views action inputs tables).1 =
      2 * ((List.ofFn (fun index => ((inputs index).1.map exprNodeCount).sum +
        ((tables index).1.map exprNodeCount).sum)).sum *
          (node + 1 + access + costs.add + costs.negate + costs.multiply) +
        (List.ofFn (fun index => (inputs index).1.length + (tables index).1.length)).sum *
          (access + costs.multiply + costs.add + 2) + 2) +
        50 * access + 100 * (costs.add + costs.negate + costs.multiply + 1) := by
    simp only [subProofLookupCostBudget, plonkLookupInputsCosted_nodes, plonkLookupInputsCosted_width]
  simp only [subProofConstraintCostBudget, plonkPermutationSetsCosted_length,
    plonkLookupInputsCosted_length, hlookup]
  dsimp only [plonkPreparedConstraintCostBudget]
  omega


end Zcash.Snark.ZeroKnowledge
