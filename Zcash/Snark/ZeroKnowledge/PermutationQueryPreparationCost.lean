import Zcash.Snark.ZeroKnowledge.QueryRoutingCost
import Zcash.Snark.ZeroKnowledge.ConstraintAssemblyCost

/-!
# Counted preparation of the verifier's permutation chunks

The original column reference and sigma index are resolved with their complete
query-reader costs. Prepared scalar pairs are materialized, then paired with
the original permutation sets using the verifier's truncating zip semantics.
All input preparation, traversal, and output construction costs are retained.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Resolve and materialize a column/sigma pair from the actual key entry. -/
def permutationColumnPairCosted (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (entry : ColumnRef × ℕ) : ((Fp × Fp) × ℕ) × ℕ :=
  let column := columnResolveCosted entry.1 instanceRead advice fixed
  let permutation := sigma entry.2
  (((column.1, permutation.1), 1), column.2 + permutation.2 + 3)

/-- Erasure is the original resolved column and sigma claim. -/
theorem permutationColumnPairCosted_result (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (entry : ColumnRef × ℕ) :
    (permutationColumnPairCosted instanceRead advice fixed sigma entry).1.1 =
      (entry.1.resolve (fun index => (instanceRead index).1) (fun index => (advice index).1)
        (fun index => (fixed index).1), (sigma entry.2).1) := by
  simp only [permutationColumnPairCosted, columnResolveCosted_result]

/-- Every scalar pair is fully materialized before the constraint fold reads it. -/
theorem permutationColumnPairCosted_readCost (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (entry : ColumnRef × ℕ) :
    (permutationColumnPairCosted instanceRead advice fixed sigma entry).1.2 = 1 := rfl

/-- Both complete scalar-reader costs and the column selection are included. -/
theorem permutationColumnPairCosted_cost_le (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (entry : ColumnRef × ℕ) (access : ℕ)
    (hi : ∀ index, (instanceRead index).2 ≤ access) (ha : ∀ index, (advice index).2 ≤ access)
    (hf : ∀ index, (fixed index).2 ≤ access) (hs : ∀ index, (sigma index).2 ≤ access) :
    (permutationColumnPairCosted instanceRead advice fixed sigma entry).2 ≤ 2 * access + 4 := by
  have hc := columnResolveCosted_cost_le entry.1 instanceRead advice fixed access hi ha hf
  have hp := hs entry.2
  simp only [permutationColumnPairCosted]
  omega

/-- Prepare one complete original permutation chunk and retain its set record. -/
def permutationQueryChunkCosted (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (entry : PermSetEval (Fp × ℕ) × List (ColumnRef × ℕ)) :
    (PermSetEval (Fp × ℕ) × List ((Fp × Fp) × ℕ)) × ℕ :=
  let columns := mapListCosted (permutationColumnPairCosted instanceRead advice fixed sigma) entry.2
  ((entry.1, columns.1), columns.2 + 2)

/-- The materialized chunk keeps every original key entry and its resolved scalar pair. -/
theorem permutationQueryChunkCosted_result (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (entry : PermSetEval (Fp × ℕ) × List (ColumnRef × ℕ)) :
    let result := (permutationQueryChunkCosted instanceRead advice fixed sigma entry).1
    (result.1.map Prod.fst, result.2.map Prod.fst) =
      (entry.1.map Prod.fst, entry.2.map (fun reference =>
        (reference.1.resolve (fun index => (instanceRead index).1) (fun index => (advice index).1)
          (fun index => (fixed index).1), (sigma reference.2).1))) := by
  simp only [permutationQueryChunkCosted, mapListCosted_result, List.map_map, Function.comp_def,
    permutationColumnPairCosted_result]

/-- A complete chunk pays for all column routes and output pair cells. -/
theorem permutationQueryChunkCosted_cost_le (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (entry : PermSetEval (Fp × ℕ) × List (ColumnRef × ℕ)) (access : ℕ)
    (hi : ∀ index, (instanceRead index).2 ≤ access) (ha : ∀ index, (advice index).2 ≤ access)
    (hf : ∀ index, (fixed index).2 ≤ access) (hs : ∀ index, (sigma index).2 ≤ access) :
    (permutationQueryChunkCosted instanceRead advice fixed sigma entry).2 ≤
      entry.2.length * (2 * access + 5) + 3 := by
  have h := mapListCosted_cost_le (permutationColumnPairCosted instanceRead advice fixed sigma)
    entry.2 (2 * access + 4)
    (fun reference _ => permutationColumnPairCosted_cost_le instanceRead advice fixed sigma reference access hi ha hf hs)
  simp only [permutationQueryChunkCosted]
  nlinarith

/-- Prepare all original chunks, retaining the full set and layout input preparation. -/
def permutationQueryChunksCosted (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (sets : List (PermSetEval (Fp × ℕ)) × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ) :
    List (PermSetEval (Fp × ℕ) × List ((Fp × Fp) × ℕ)) × ℕ :=
  let pairs := zipListCosted sets.1 layout.1
  let result := mapListCosted (permutationQueryChunkCosted instanceRead advice fixed sigma) pairs.1
  (result.1, sets.2 + layout.2 + pairs.2 + result.2 + 1)

/-- Erasure preserves the verifier's full truncating set/layout zip and subsequent resolution. -/
theorem permutationQueryChunksCosted_result (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (sets : List (PermSetEval (Fp × ℕ)) × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ) :
    (permutationQueryChunksCosted instanceRead advice fixed sigma sets layout).1.map
        (fun chunk => (chunk.1.map Prod.fst, chunk.2.map Prod.fst)) =
      ((sets.1.map (PermSetEval.map Prod.fst)).zip layout.1).map (fun entry =>
        (entry.1, entry.2.map (fun reference =>
          (reference.1.resolve (fun index => (instanceRead index).1) (fun index => (advice index).1)
            (fun index => (fixed index).1), (sigma reference.2).1)))) := by
  simp only [permutationQueryChunksCosted, mapListCosted_result, zipListCosted_result,
    List.map_map, Function.comp_def, permutationQueryChunkCosted_result, List.zip_map_left]
  rfl

/-- Preparation creates at most one chunk per materialized permutation set. -/
theorem permutationQueryChunksCosted_length_le (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (sets : List (PermSetEval (Fp × ℕ)) × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ) :
    (permutationQueryChunksCosted instanceRead advice fixed sigma sets layout).1.length ≤ sets.1.length := by
  simp only [permutationQueryChunksCosted, mapListCosted_result, zipListCosted_result,
    List.length_map, List.length_zip]
  exact Nat.min_le_left _ _

/-- The full preparation budget uses the actual stored key-entry count and complete query prices. -/
theorem permutationQueryChunksCosted_cost_le (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (sets : List (PermSetEval (Fp × ℕ)) × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ)
    (access : ℕ)
    (hi : ∀ index, (instanceRead index).2 ≤ access) (ha : ∀ index, (advice index).2 ≤ access)
    (hf : ∀ index, (fixed index).2 ≤ access) (hs : ∀ index, (sigma index).2 ≤ access) :
    (permutationQueryChunksCosted instanceRead advice fixed sigma sets layout).2 ≤
      sets.2 + layout.2 +
        sets.1.length * ((layout.1.map List.length).sum * (2 * access + 5) + 6) + 3 := by
  let pairs := zipListCosted sets.1 layout.1
  let budget := (layout.1.map List.length).sum * (2 * access + 5) + 3
  have hzip := zipListCosted_cost_le sets.1 layout.1
  have hlength : pairs.1.length ≤ sets.1.length := by
    simp only [pairs, zipListCosted_result, List.length_zip]
    exact Nat.min_le_left _ _
  have hmap := mapListCosted_cost_le (permutationQueryChunkCosted instanceRead advice fixed sigma)
    pairs.1 budget (fun entry hmem => by
      have hpair : entry ∈ sets.1.zip layout.1 := by simpa only [pairs, zipListCosted_result] using hmem
      have hentry := listValue_le_map_sum List.length layout.1 entry.2 (List.of_mem_zip hpair).2
      exact (permutationQueryChunkCosted_cost_le instanceRead advice fixed sigma entry access hi ha hf hs).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ hentry) 3))
  have hscaled := Nat.mul_le_mul_right (budget + 1) hlength
  change sets.2 + layout.2 + pairs.2 +
    (mapListCosted (permutationQueryChunkCosted instanceRead advice fixed sigma) pairs.1).2 + 1 ≤ _
  change pairs.2 ≤ _ at hzip
  dsimp only [budget] at hmap hscaled
  nlinarith

end Zcash.Snark.ZeroKnowledge
