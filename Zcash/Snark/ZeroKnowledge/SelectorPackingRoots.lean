import Clean.Halo2.Keygen.CompressSelectors

/-!
# Root coordinates in selector-compression columns

Every selector assigned to one packed column receives a root between one and the
column's combination length. Equal roots in the same column name the same source
selector. These facts depend on the packer's indexed output construction, for
every activation pattern and degree budget.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Equal positions in an indexed list name the same value, preventing distinct selector groups from
sharing an index accidentally. -/
private theorem zipIdx_fst_eq {α : Type} (items : List α) {left right : α × ℕ}
    (hleft : left ∈ items.zipIdx) (hright : right ∈ items.zipIdx)
    (hindex : left.2 = right.2) : left.1 = right.1 := by
  rcases left with ⟨left, index⟩
  rcases right with ⟨right, otherIndex⟩
  simp only at hindex
  subst otherIndex
  exact Option.some.inj <|
    (List.mk_mem_zipIdx_iff_getElem?.mp hleft).symm.trans
      (List.mk_mem_zipIdx_iff_getElem?.mp hright)

/-- Entries in one output column have the same length, valid roots, and unique
source-selector coordinates. No property of the activation arrays is required. -/
theorem process_entry_root_coordinates (selectors : List SelectorDescription) (maxDegree : ℕ)
    (left right : ℕ × SelCompress)
    (hleft : left ∈ (process selectors maxDegree).entries)
    (hright : right ∈ (process selectors maxDegree).entries)
    (hcolumn : left.2.packedCol = right.2.packedCol) :
    left.2.combinationLen = right.2.combinationLen ∧
      1 ≤ right.2.assignedRoot ∧ right.2.assignedRoot ≤ left.2.combinationLen ∧
      (left.2.assignedRoot = right.2.assignedRoot → left.1 = right.1) := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations := buildCombinations maxDegree remaining.length remaining
  change left ∈
      (degreeZero.zipIdx.map fun (description, column) =>
        (description.selector, SelCompress.mk column 1 1)) ++
      (combinations.zipIdx.flatMap fun (combination, column) =>
        combination.zipIdx.map fun (description, position) =>
          (description.selector, SelCompress.mk (degreeZero.length + column)
            combination.length (position + 1))) at hleft
  change right ∈
      (degreeZero.zipIdx.map fun (description, column) =>
        (description.selector, SelCompress.mk column 1 1)) ++
      (combinations.zipIdx.flatMap fun (combination, column) =>
        combination.zipIdx.map fun (description, position) =>
          (description.selector, SelCompress.mk (degreeZero.length + column)
            combination.length (position + 1))) at hright
  rw [List.mem_append] at hleft hright
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · obtain ⟨leftIndexed, hleftIndexed, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightIndexed, hrightIndexed, rfl⟩ := List.mem_map.mp hright
    refine ⟨rfl, le_rfl, le_rfl, fun _ => ?_⟩
    exact congrArg SelectorDescription.selector (zipIdx_fst_eq degreeZero hleftIndexed hrightIndexed hcolumn)
  · obtain ⟨leftIndexed, hleftIndexed, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightCombination, _, hright⟩ := List.mem_flatMap.mp hright
    obtain ⟨rightIndexed, _, rfl⟩ := List.mem_map.mp hright
    have hleftColumn := List.snd_lt_of_mem_zipIdx hleftIndexed
    simp only at hcolumn
    omega
  · obtain ⟨leftCombination, _, hleft⟩ := List.mem_flatMap.mp hleft
    obtain ⟨leftIndexed, _, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightIndexed, hrightIndexed, rfl⟩ := List.mem_map.mp hright
    have hrightColumn := List.snd_lt_of_mem_zipIdx hrightIndexed
    simp only at hcolumn
    omega
  · obtain ⟨⟨leftItems, leftColumn⟩, hleftCombination, hleft⟩ := List.mem_flatMap.mp hleft
    obtain ⟨⟨rightItems, rightColumn⟩, hrightCombination, hright⟩ := List.mem_flatMap.mp hright
    obtain ⟨⟨leftDescription, leftPosition⟩, hleftIndexed, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨⟨rightDescription, rightPosition⟩, hrightIndexed, rfl⟩ := List.mem_map.mp hright
    have hcombinationColumn : leftColumn = rightColumn := by
      simp only at hcolumn
      omega
    have hcombination := zipIdx_fst_eq combinations hleftCombination hrightCombination hcombinationColumn
    dsimp at hcombination
    subst rightItems
    have hrightPosition := List.snd_lt_of_mem_zipIdx hrightIndexed
    dsimp only at hrightPosition ⊢
    refine ⟨rfl, by omega, by simpa using hrightPosition, ?_⟩
    intro hroot
    have hposition : leftPosition = rightPosition := by
      omega
    exact congrArg SelectorDescription.selector (zipIdx_fst_eq leftItems hleftIndexed hrightIndexed hposition)

/-- Prefixing the new columns with the original fixed columns preserves all root
coordinates in the circuit-derived compression map. -/
theorem deriveSelCompressMap_lookup_root_coordinates {F : Type}
    (cs : ConstraintSystem F) (n : ℕ) (acts : List (ℕ × ℕ))
    {leftSelector rightSelector : ℕ} {left right : SelCompress}
    (hleft : (deriveSelCompressMap cs n acts).lookup leftSelector = some left)
    (hright : (deriveSelCompressMap cs n acts).lookup rightSelector = some right)
    (hcolumn : left.packedCol = right.packedCol) :
    left.combinationLen = right.combinationLen ∧
      1 ≤ right.assignedRoot ∧ right.assignedRoot ≤ left.combinationLen ∧
      (left.assignedRoot = right.assignedRoot → leftSelector = rightSelector) := by
  let table := activationTable n cs.numSelectors acts
  let degrees := selectorMaxDegrees cs
  let descriptions := (List.range cs.numSelectors).map fun index =>
    SelectorDescription.mk index table[index]! degrees[index]!
  let packing := process descriptions (csDegree cs)
  have hleftEntry := SelCompressMap.mem_entries_of_lookup (deriveSelCompressMap cs n acts) hleft
  have hrightEntry := SelCompressMap.mem_entries_of_lookup (deriveSelCompressMap cs n acts) hright
  change (leftSelector, left) ∈ packing.entries.map (fun (selector, compressed) =>
    (selector, { compressed with packedCol := compressed.packedCol + cs.numFixedColumns })) at hleftEntry
  change (rightSelector, right) ∈ packing.entries.map (fun (selector, compressed) =>
    (selector, { compressed with packedCol := compressed.packedCol + cs.numFixedColumns })) at hrightEntry
  obtain ⟨⟨leftSourceSelector, leftSource⟩, hleftSource, hleftEq⟩ := List.mem_map.mp hleftEntry
  obtain ⟨⟨rightSourceSelector, rightSource⟩, hrightSource, hrightEq⟩ := List.mem_map.mp hrightEntry
  simp only [Prod.mk.injEq] at hleftEq hrightEq
  rcases hleftEq with ⟨rfl, rfl⟩
  rcases hrightEq with ⟨rfl, rfl⟩
  exact process_entry_root_coordinates descriptions (csDegree cs)
    (leftSourceSelector, leftSource) (rightSourceSelector, rightSource)
    hleftSource hrightSource (Nat.add_right_cancel hcolumn)

end Zcash.Snark.ZeroKnowledge
