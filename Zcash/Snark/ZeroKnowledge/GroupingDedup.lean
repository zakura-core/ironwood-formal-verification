import Zcash.Snark.Verifier.GroupingRef
import Mathlib.Data.List.Dedup

/-!
# First-appearance deduplication of disjoint query blocks

The verifier keeps each commitment's first appearance. Action blocks have disjoint
commitment IDs, so their deduplication can be proved once per block and composed
without evaluating a growing query list in the kernel.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {α β : Type*} [DecidableEq α]

/-- First-appearance deduplication is reverse-order last-appearance deduplication. -/
theorem groupingDedup_reverse (values : List α) :
    dedupFold values = values.reverse.dedup.reverse := by
  induction values using List.reverseRecOn with
  | nil => rfl
  | append_singleton values value ih =>
    rw [dedupFold, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (if value ∈ dedupFold values then dedupFold values
      else dedupFold values ++ [value]) = _
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.dedup_cons]
    by_cases h : value ∈ values <;> simp [h, ih]

/-- Disjoint blocks keep their first-appearance order independently. -/
theorem groupingDedup_append_disjoint (left right : List α) (hdisjoint : List.Disjoint left right) :
    dedupFold (left ++ right) = dedupFold left ++ dedupFold right := by
  simp only [groupingDedup_reverse, List.reverse_append]
  have hreverse : List.Disjoint right.reverse left.reverse := by
    intro value hright hleft
    exact hdisjoint (List.mem_reverse.mp hleft) (List.mem_reverse.mp hright)
  rw [hreverse.dedup_append, List.reverse_append]

/-- A later block whose values have all appeared adds nothing to the first-appearance table. -/
theorem groupingDedup_append_subset (left right : List α) (hsubset : right ⊆ left) :
    dedupFold (left ++ right) = dedupFold left := by
  rw [groupingDedup_reverse, List.reverse_append]
  have hreverse : right.reverse ⊆ left.reverse := by
    intro value hvalue
    exact List.mem_reverse.mpr (hsubset (List.mem_reverse.mp hvalue))
  rw [hreverse.dedup_append_right, ← groupingDedup_reverse]

/-- A duplicate-free list of pairwise-disjoint query blocks deduplicates block by block. -/
theorem groupingDedup_flatMap (blocks : List β) (entries : β → List α)
    (hnodup : blocks.Nodup)
    (hdisjoint : ∀ a ∈ blocks, ∀ b ∈ blocks, a ≠ b → List.Disjoint (entries a) (entries b)) :
    dedupFold (blocks.flatMap entries) = blocks.flatMap (fun a => dedupFold (entries a)) := by
  induction blocks with
  | nil => rfl
  | cons a blocks ih =>
    have htail := List.nodup_cons.mp hnodup
    have hab : List.Disjoint (entries a) (blocks.flatMap entries) := by
      intro value ha hb
      obtain ⟨b, hb, hvalue⟩ := List.mem_flatMap.mp hb
      exact hdisjoint a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
        (fun h => htail.1 (h ▸ hb)) ha hvalue
    rw [List.flatMap_cons, groupingDedup_append_disjoint _ _ hab,
      ih htail.2 (fun b hb c hc hbc =>
        hdisjoint b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) hbc), List.flatMap_cons]

end Zcash.Snark.ZeroKnowledge
