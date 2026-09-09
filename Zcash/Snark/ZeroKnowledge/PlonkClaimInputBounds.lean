import Zcash.Snark.ZeroKnowledge.PlonkClaimInputsCost
import Zcash.Snark.ZeroKnowledge.PlonkLookupInputsCost
import Zcash.Snark.ZeroKnowledge.PermutationQueryPreparationCost

/-!
# Sizes and access bounds of the actual prepared PLONK claims

These bounds follow from the constructed lists and records. They do not assume
that an arbitrary preparation callback happens to satisfy the constraint
evaluator's premises. All scalar fields are materialized, while expression sizes
are measured on the supplied key data.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- A larger access budget preserves all optional permutation-field bounds. -/
theorem permSetReadBound_mono {F : Type*} {set : PermSetEval (F × ℕ)} {small large : ℕ}
    (hset : permSetReadBound set small) (hle : small ≤ large) : permSetReadBound set large :=
  ⟨hset.1.trans hle, hset.2.1.trans hle, fun value hmem => (hset.2.2 value hmem).trans hle⟩

/-- A larger access budget preserves every stored lookup-field bound. -/
theorem lookupEvalReadBound_mono {F : Type*} {evaluation : LookupEval (F × ℕ)} {small large : ℕ}
    (hlookup : lookupEvalReadBound evaluation small) (hle : small ≤ large) :
    lookupEvalReadBound evaluation large :=
  ⟨hlookup.1.trans hle, hlookup.2.1.trans hle, hlookup.2.2.1.trans hle,
    hlookup.2.2.2.1.trans hle, hlookup.2.2.2.2.trans hle⟩

/-- Every member of the actual permutation-set list has unit stored-field access. -/
theorem plonkPermutationSetsCosted_readBound (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (set : PermSetEval (Fp × ℕ)) (hmem : set ∈ (plonkPermutationSetsCosted equal read views action).1) :
    permSetReadBound set 1 := by
  simp only [plonkPermutationSetsCosted, ofFnCosted_result, List.mem_ofFn] at hmem
  obtain ⟨index, rfl⟩ := hmem
  exact plonkPermutationSetCosted_readBound equal read views action index

/-- Prepared chunks retain the original set bounds and materialize every scalar pair. -/
theorem permutationQueryChunksCosted_readBound (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (sets : List (PermSetEval (Fp × ℕ)) × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ)
    (hsets : ∀ set ∈ sets.1, permSetReadBound set 1)
    (chunk : PermSetEval (Fp × ℕ) × List ((Fp × Fp) × ℕ))
    (hmem : chunk ∈ (permutationQueryChunksCosted instanceRead advice fixed sigma sets layout).1) :
    permSetReadBound chunk.1 1 ∧ ∀ pair ∈ chunk.2, pair.2 ≤ 1 := by
  simp only [permutationQueryChunksCosted, mapListCosted_result, zipListCosted_result,
    List.mem_map] at hmem
  obtain ⟨entry, hentry, rfl⟩ := hmem
  refine ⟨hsets entry.1 (List.of_mem_zip hentry).1, ?_⟩
  intro pair hpair
  simp only [permutationQueryChunkCosted, mapListCosted_result, List.mem_map] at hpair
  obtain ⟨reference, _, rfl⟩ := hpair
  exact le_rfl

/-- Every prepared chunk has at most the actual total number of key entries. -/
theorem permutationQueryChunksCosted_entry_length_le (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (sets : List (PermSetEval (Fp × ℕ)) × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ)
    (chunk : PermSetEval (Fp × ℕ) × List ((Fp × Fp) × ℕ))
    (hmem : chunk ∈ (permutationQueryChunksCosted instanceRead advice fixed sigma sets layout).1) :
    chunk.2.length ≤ (layout.1.map List.length).sum := by
  simp only [permutationQueryChunksCosted, mapListCosted_result, zipListCosted_result,
    List.mem_map] at hmem
  obtain ⟨entry, hentry, rfl⟩ := hmem
  simp only [permutationQueryChunkCosted, mapListCosted_result, List.length_map]
  exact listValue_le_map_sum List.length layout.1 entry.2 (List.of_mem_zip hentry).2

/-- The aggregate prepared-column size is bounded by set count times stored layout size. -/
theorem permutationQueryChunksCosted_columns_le (instanceRead advice fixed sigma : ℕ → Fp × ℕ)
    (sets : List (PermSetEval (Fp × ℕ)) × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ) :
    ((permutationQueryChunksCosted instanceRead advice fixed sigma sets layout).1.map
      (fun chunk => chunk.2.length)).sum ≤ sets.1.length * (layout.1.map List.length).sum := by
  let chunks := (permutationQueryChunksCosted instanceRead advice fixed sigma sets layout).1
  have hentry : ∀ chunk ∈ chunks, chunk.2.length ≤ (layout.1.map List.length).sum :=
    permutationQueryChunksCosted_entry_length_le instanceRead advice fixed sigma sets layout
  have hsum : (chunks.map (fun chunk => chunk.2.length)).sum ≤
      (chunks.map (fun _ => (layout.1.map List.length).sum)).sum := List.sum_le_sum hentry
  have hsum' : (chunks.map (fun chunk => chunk.2.length)).sum ≤
      chunks.length * (layout.1.map List.length).sum := by simpa using hsum
  exact hsum'.trans (Nat.mul_le_mul_right _
    (permutationQueryChunksCosted_length_le instanceRead advice fixed sigma sets layout))

/-- Every member of the complete lookup list has unit stored-scalar access. -/
theorem plonkLookupInputsCosted_readBound (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    (lookup : LookupEval (Fp × ℕ) × List (Expr Fp) × List (Expr Fp))
    (hmem : lookup ∈ (plonkLookupInputsCosted equal read views action inputs tables).1) :
    lookupEvalReadBound lookup.1 1 := by
  simp only [plonkLookupInputsCosted, ofFnCosted_result, List.mem_ofFn] at hmem
  obtain ⟨index, rfl⟩ := hmem
  exact plonkLookupInputCosted_readBound equal read views action inputs tables index

/-- The exact lookup-node total depends only on the supplied expression trees. -/
theorem plonkLookupInputsCosted_nodes (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) :
    ((plonkLookupInputsCosted equal read views action inputs tables).1.map (fun lookup =>
      (lookup.2.1.map exprNodeCount).sum + (lookup.2.2.map exprNodeCount).sum)).sum =
      (List.ofFn (fun index => ((inputs index).1.map exprNodeCount).sum +
        ((tables index).1.map exprNodeCount).sum)).sum := by
  simp only [plonkLookupInputsCosted, ofFnCosted_result, List.map_ofFn, Function.comp_def,
    plonkLookupInputCosted]

/-- The exact lookup-expression width is its actual stored input and table list size. -/
theorem plonkLookupInputsCosted_width (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) :
    ((plonkLookupInputsCosted equal read views action inputs tables).1.map (fun lookup =>
      lookup.2.1.length + lookup.2.2.length)).sum =
      (List.ofFn (fun index => (inputs index).1.length + (tables index).1.length)).sum := by
  simp only [plonkLookupInputsCosted, ofFnCosted_result, List.map_ofFn, Function.comp_def,
    plonkLookupInputCosted]

end Zcash.Snark.ZeroKnowledge
