import Zcash.Snark.ZeroKnowledge.PermutationBoundaryCost
import Zcash.Snark.ZeroKnowledge.PermutationChunkCost

/-!
# Counted complete permutation constraint lists

The algorithm materializes the initial, final, chaining, and chunk constraints in
the verifier's original order. Its bound includes list routing, every indexed
chunk calculation, all optional branches, and construction of the complete list.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Count the complete permutation-expression list with its original ordered concatenations. -/
def permutationExpressionsCosted {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (beta gamma x delta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ) : List F × ℕ :=
  let first := permutationFirstCosted costs sets l0
  let last := permutationLastCosted costs sets lLast
  let adjacent := zipListCosted sets.tail sets
  let chains := mapListCosted (fun pair => permutationChainCosted costs pair.1 pair.2 l0) adjacent.1
  let values := mapIndexListCosted (fun index chunk =>
    permChunkExpressionCosted costs beta gamma x delta chunkLen index chunk.1 chunk.2 lLast lBlind) 0 chunks
  let initial := appendListCosted first.1 last.1
  let middle := appendListCosted initial.1 chains.1
  let result := appendListCosted middle.1 values.1
  (result.1, first.2 + last.2 + adjacent.2 + chains.2 + values.2 + initial.2 + middle.2 + result.2 + 1)

/-- Erasure is exactly the existing verifier's full ordered permutation constraint list. -/
theorem permutationExpressionsCosted_result {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (beta gamma x delta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ) :
    (permutationExpressionsCosted costs sets chunks beta gamma x delta chunkLen l0 lLast lBlind).1 =
      permutationExpressions (sets.map (PermSetEval.map Prod.fst))
        (chunks.map (fun chunk => (chunk.1.map Prod.fst, chunk.2.map Prod.fst)))
        beta.1 gamma.1 x.1 delta.1 chunkLen l0.1 lLast.1 lBlind.1 := by
  simp only [permutationExpressionsCosted, appendListCosted_result, permutationFirstCosted_result,
    permutationLastCosted_result, mapListCosted_result, mapIndexListCosted_result, zipListCosted_result,
    permutationChainCosted_result, permChunkExpressionCosted_result, permutationExpressions,
    List.drop_one, ← List.map_tail, List.zip_map_left, List.zip_map_right, List.map_map,
    List.length_map, List.range_eq_range', Prod.map, Function.comp_def, id_eq]
  cases (sets.map (PermSetEval.map Prod.fst)).head? <;>
    cases (sets.map (PermSetEval.map Prod.fst)).getLast? <;> rfl

/-- A common budget for every indexed chunk in a materialized chunk list. -/
def permutationChunkListCostBudget (costs : FieldOperationCosts) (access pairs count stride : ℕ) : ℕ :=
  2 * pairs * (3 * access + 2 * costs.multiply + 2 * costs.add + 5) +
    (count * stride) * (costs.multiply + 1) +
    20 * access + 20 * (costs.add + costs.negate + costs.multiply + 1)

/-- Full permutation-list execution retains every field read, traversal, and output allocation. -/
theorem permutationExpressionsCosted_cost_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (beta gamma x delta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ)
    (access pairs : ℕ) (hsets : ∀ set ∈ sets, permSetReadBound set access)
    (hchunks : ∀ chunk ∈ chunks, permSetReadBound chunk.1 access ∧ chunk.2.length ≤ pairs ∧
      ∀ pair ∈ chunk.2, pair.2 ≤ access)
    (hbeta : beta.2 ≤ access) (hgamma : gamma.2 ≤ access) (hx : x.2 ≤ access) (hdelta : delta.2 ≤ access)
    (hl0 : l0.2 ≤ access) (hlLast : lLast.2 ≤ access) (hlBlind : lBlind.2 ≤ access) :
    (permutationExpressionsCosted costs sets chunks beta gamma x delta chunkLen l0 lLast lBlind).2 ≤
      sets.length * (3 * access + costs.add + costs.negate + costs.multiply + 12) +
        chunks.length * (permutationChunkListCostBudget costs access pairs chunks.length chunkLen + 2) +
        20 * access + 30 * (costs.add + costs.negate + costs.multiply + 1) := by
  let first := permutationFirstCosted costs sets l0
  let last := permutationLastCosted costs sets lLast
  let adjacent := zipListCosted sets.tail sets
  let chains := mapListCosted (fun pair => permutationChainCosted costs pair.1 pair.2 l0) adjacent.1
  let values := mapIndexListCosted (fun index chunk =>
    permChunkExpressionCosted costs beta gamma x delta chunkLen index chunk.1 chunk.2 lLast lBlind) 0 chunks
  let initial := appendListCosted first.1 last.1
  let middle := appendListCosted initial.1 chains.1
  let result := appendListCosted middle.1 values.1
  let chunkBudget := permutationChunkListCostBudget costs access pairs chunks.length chunkLen
  have hfirst : first.2 ≤ 2 * access + costs.add + costs.negate + costs.multiply + 6 :=
    permutationFirstCosted_cost_le costs sets l0 access hsets hl0
  have hlast : last.2 ≤
      2 * sets.length + 4 * access + costs.add + costs.negate + 2 * costs.multiply + 8 :=
    permutationLastCosted_cost_le costs sets lLast access hsets hlLast
  have hfirstLength : first.1.length ≤ 1 := permutationFirstCosted_length_le costs sets l0
  have hlastLength : last.1.length ≤ 1 := permutationLastCosted_length_le costs sets lLast
  have hadjacentLength : adjacent.1.length ≤ sets.length := by
    simp only [adjacent, zipListCosted_result, List.length_zip]
    exact min_le_right _ _
  have hadjacent : adjacent.2 ≤ 2 * sets.length + 1 := by
    have h := zipListCosted_cost_le sets.tail sets
    simp only [List.length_tail] at h
    dsimp only [adjacent]
    omega
  have hchains : chains.2 ≤
      sets.length * (3 * access + costs.add + costs.negate + costs.multiply + 5) + 1 := by
    have h := mapListCosted_cost_le (fun pair => permutationChainCosted costs pair.1 pair.2 l0) adjacent.1
      (3 * access + costs.add + costs.negate + costs.multiply + 4) (fun pair hpair => by
        have hmem : pair ∈ sets.tail.zip sets := by simpa only [adjacent, zipListCosted_result] using hpair
        have hboth := List.of_mem_zip hmem
        exact permutationChainCosted_cost_le costs pair.1 pair.2 l0 access
          (hsets pair.1 (List.mem_of_mem_tail hboth.1)) (hsets pair.2 hboth.2) hl0)
    refine h.trans ?_
    gcongr
  have hchainsLength : chains.1.length ≤ sets.length := by
    simpa only [chains, mapListCosted_result, List.length_map] using hadjacentLength
  have hvalues : values.2 ≤ chunks.length * (chunkBudget + 2) + 1 := by
    apply mapIndexListCosted_cost_le
    intro index _ hindex chunk hchunk
    rcases hchunks chunk hchunk with ⟨hset, hlength, hreads⟩
    refine (permChunkExpressionCosted_cost_le costs beta gamma x delta chunkLen index
      chunk.1 chunk.2 lLast lBlind access hbeta hgamma hx hdelta hset.1 hset.2.1 hreads hlLast hlBlind).trans ?_
    have hindexLe : index ≤ chunks.length := by omega
    dsimp only [chunkBudget, permutationChunkListCostBudget]
    gcongr
  have hinitial : initial.2 ≤ 2 := by
    change (appendListCosted first.1 last.1).2 ≤ 2
    rw [appendListCosted_cost]
    omega
  have hinitialLength : initial.1.length ≤ 2 := by
    simp only [initial, appendListCosted_result, List.length_append]
    omega
  have hmiddle : middle.2 ≤ 3 := by
    change (appendListCosted initial.1 chains.1).2 ≤ 3
    rw [appendListCosted_cost]
    omega
  have hmiddleLength : middle.1.length ≤ sets.length + 2 := by
    simp only [middle, appendListCosted_result, List.length_append]
    omega
  have hresult : result.2 ≤ sets.length + 3 := by
    change (appendListCosted middle.1 values.1).2 ≤ sets.length + 3
    rw [appendListCosted_cost]
    omega
  change first.2 + last.2 + adjacent.2 + chains.2 + values.2 + initial.2 + middle.2 + result.2 + 1 ≤ _
  have hsplit :
      sets.length * (3 * access + costs.add + costs.negate + costs.multiply + 12) =
        sets.length * (3 * access + costs.add + costs.negate + costs.multiply + 5) + 7 * sets.length := by ring
  rw [hsplit]
  change first.2 + last.2 + adjacent.2 + chains.2 + values.2 + initial.2 + middle.2 + result.2 + 1 ≤
    sets.length * (3 * access + costs.add + costs.negate + costs.multiply + 5) + 7 * sets.length +
      chunks.length * (chunkBudget + 2) + 20 * access + 30 * (costs.add + costs.negate + costs.multiply + 1)
  omega

end Zcash.Snark.ZeroKnowledge
