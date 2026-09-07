import Zcash.Snark.ZeroKnowledge.PlonkColumns

/-!
# Read-before-construction bounds for the private-column order

Advice occupies the first `10m` positions. Lookup permutations occupy the next
`6m`, followed by `3m` permutation products and `3m` lookup products. Consequently
every non-advice construction can read all advice columns, and lookup products can
also read all lookup permutation columns from their preceding private history.
-/

namespace Zcash.Snark.ZeroKnowledge

private theorem idxOf_block_bounds {A : Type*} [DecidableEq A]
    (before block after : List A) (value : A) (hbefore : value ∉ before) (hblock : value ∈ block) :
    before.length ≤ (before ++ block ++ after).idxOf value ∧
      (before ++ block ++ after).idxOf value < before.length + block.length := by
  simp only [List.append_assoc, List.idxOf_append_of_notMem hbefore, List.idxOf_append_of_mem hblock]
  have h := List.idxOf_lt_length_of_mem hblock
  omega

/-- The exact four phase ranges in the actual commitment schedule. -/
theorem privateColumnIndex_bounds {actions : ℕ} (id : PrivateColumnId actions) :
    match id with
    | .advice _ _ => (privateColumnIndex id).val < 10 * actions
    | .lookupInput _ _ | .lookupTable _ _ =>
      10 * actions ≤ (privateColumnIndex id).val ∧ (privateColumnIndex id).val < 16 * actions
    | .permutationProduct _ _ =>
      16 * actions ≤ (privateColumnIndex id).val ∧ (privateColumnIndex id).val < 19 * actions
    | .lookupProduct _ _ =>
      19 * actions ≤ (privateColumnIndex id).val ∧ (privateColumnIndex id).val < 22 * actions := by
  let advice : List (PrivateColumnId actions) :=
    (List.finRange actions).flatMap (fun a => (List.finRange 10).map (.advice a))
  let lookup : List (PrivateColumnId actions) :=
    (List.finRange actions).flatMap (fun a => (List.finRange 3).flatMap
      (fun l => [.lookupInput a l, .lookupTable a l]))
  let permutation : List (PrivateColumnId actions) :=
    (List.finRange actions).flatMap (fun a => (List.finRange 3).map (.permutationProduct a))
  let product : List (PrivateColumnId actions) :=
    (List.finRange actions).flatMap (fun a => (List.finRange 3).map (.lookupProduct a))
  have ha : advice.length = 10 * actions := by
    simp [advice, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  have hl : lookup.length = 6 * actions := by
    simp [lookup, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  have hp : permutation.length = 3 * actions := by
    simp [permutation, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  have hd : product.length = 3 * actions := by
    simp [product, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  cases id with
  | advice a c =>
    change (advice ++ lookup ++ permutation ++ product).idxOf (.advice a c) < 10 * actions
    have h := idxOf_block_bounds [] advice (lookup ++ permutation ++ product) (.advice a c)
      (by simp) (by simp [advice, List.mem_flatMap])
    simpa only [List.append_assoc, List.nil_append, List.length_nil, zero_add, ha] using h.2
  | lookupInput a l =>
    change 10 * actions ≤ (advice ++ lookup ++ permutation ++ product).idxOf (.lookupInput a l) ∧
      (advice ++ lookup ++ permutation ++ product).idxOf (.lookupInput a l) < 16 * actions
    have h := idxOf_block_bounds advice lookup (permutation ++ product) (.lookupInput a l)
      (by simp [advice, List.mem_flatMap]) (by simp [lookup, List.mem_flatMap])
    simp only [List.append_assoc, ha, hl] at h ⊢
    omega
  | lookupTable a l =>
    change 10 * actions ≤ (advice ++ lookup ++ permutation ++ product).idxOf (.lookupTable a l) ∧
      (advice ++ lookup ++ permutation ++ product).idxOf (.lookupTable a l) < 16 * actions
    have h := idxOf_block_bounds advice lookup (permutation ++ product) (.lookupTable a l)
      (by simp [advice, List.mem_flatMap]) (by simp [lookup, List.mem_flatMap])
    simp only [List.append_assoc, ha, hl] at h ⊢
    omega
  | permutationProduct a s =>
    change 16 * actions ≤ (advice ++ lookup ++ permutation ++ product).idxOf (.permutationProduct a s) ∧
      (advice ++ lookup ++ permutation ++ product).idxOf (.permutationProduct a s) < 19 * actions
    have h := idxOf_block_bounds (advice ++ lookup) permutation product (.permutationProduct a s)
      (by simp [advice, lookup, List.mem_flatMap]) (by simp [permutation, List.mem_flatMap])
    simp only [List.append_assoc, List.length_append, ha, hl, hp] at h ⊢
    omega
  | lookupProduct a l =>
    change 19 * actions ≤ (advice ++ lookup ++ permutation ++ product).idxOf (.lookupProduct a l) ∧
      (advice ++ lookup ++ permutation ++ product).idxOf (.lookupProduct a l) < 22 * actions
    have h := idxOf_block_bounds (advice ++ lookup ++ permutation) product [] (.lookupProduct a l)
      (by simp [advice, lookup, permutation, List.mem_flatMap]) (by simp [product, List.mem_flatMap])
    simp only [List.append_nil, List.append_assoc, List.length_append, ha, hl, hp, hd] at h ⊢
    omega

end Zcash.Snark.ZeroKnowledge
