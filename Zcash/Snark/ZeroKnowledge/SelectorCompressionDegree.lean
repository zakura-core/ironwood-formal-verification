import Zcash.Circuits.Integration.SelectorCoherence

/-!
# The selector packer's degree budget

The greedy compressor checks the gate degree as well as the number of selectors
sharing a column. These lemmas retain that stronger invariant: each selected
description's original degree minus one, plus its final replacement length, fits
the budget. Conflict tests may return either value; the degree argument does not
depend on the activation rows or on a particular packing trace.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Extending a combination preserves every member's original-degree-plus-replacement budget. -/
theorem extendCombination_degree_budget (budget degree : ℕ)
    (combination candidates : List SelectorDescription)
    (hroom : degree + combination.length ≤ budget)
    (hdegrees : ∀ selected ∈ combination, selected.maxDegree - 1 ≤ degree) :
    ∀ selected ∈ (extendCombination budget degree combination candidates).1,
      selected.maxDegree - 1 + (extendCombination budget degree combination candidates).1.length ≤ budget := by
  induction candidates generalizing degree combination with
  | nil =>
      intro selected hselected
      exact (Nat.add_le_add_right (hdegrees selected hselected) combination.length).trans hroom
  | cons candidate candidates ih =>
      simp only [extendCombination]
      split
      · intro selected hselected
        exact (Nat.add_le_add_right (hdegrees selected hselected) combination.length).trans hroom
      · split
        · exact ih degree combination hroom hdegrees
        · split
          · exact ih degree combination hroom hdegrees
          · apply ih
            · simp only [List.length_append, List.length_singleton]
              omega
            · intro selected hselected
              rcases List.mem_append.mp hselected with hprevious | hnew
              · exact (hdegrees selected hprevious).trans (Nat.le_max_left _ _)
              · have : selected = candidate := List.mem_singleton.mp hnew
                subst selected
                exact Nat.le_max_right _ _

/-- Every greedy output combination respects the stronger degree budget of each source member. -/
theorem buildCombinations_degree_budget (budget fuel : ℕ) (hpositive : 1 ≤ budget)
    (selectors combination : List SelectorDescription)
    (hdegrees : selectors.Forall fun selected => selected.maxDegree ≤ budget)
    (hcombination : combination ∈ buildCombinations budget fuel selectors) :
    ∀ selected ∈ combination, selected.maxDegree - 1 + combination.length ≤ budget := by
  induction fuel generalizing selectors with
  | zero => simp [buildCombinations] at hcombination
  | succ fuel ih =>
      cases selectors with
      | nil => simp [buildCombinations] at hcombination
      | cons selector rest =>
          rw [List.forall_cons] at hdegrees
          simp only [buildCombinations, List.mem_cons] at hcombination
          rcases hcombination with rfl | hremaining
          · apply extendCombination_degree_budget
            · simp only [List.length_singleton]
              omega
            · intro selected hselected
              exact List.mem_singleton.mp hselected ▸ Nat.le_refl _
          · have hpartition := extendCombination_forall budget (selector.maxDegree - 1)
              [selector] rest (fun selected => selected.maxDegree ≤ budget)
              (by simpa using hdegrees.1) hdegrees.2
            exact ih _ hpartition.2 hremaining

/-- Every emitted entry keeps its source degree and the corresponding final replacement budget. -/
theorem process_entry_degree_budget (selectors : List SelectorDescription) (budget : ℕ)
    (hpositive : 1 ≤ budget)
    (hdegrees : selectors.Forall fun selected => selected.maxDegree ≤ budget)
    (entry : ℕ × SelCompress) (hentry : entry ∈ (process selectors budget).entries) :
    ∃ source ∈ selectors, source.selector = entry.1 ∧
      if source.maxDegree = 0 then entry.2.combinationLen = 1
      else source.maxDegree - 1 + entry.2.combinationLen ≤ budget := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations := buildCombinations budget remaining.length remaining
  change entry ∈
    (degreeZero.zipIdx.map fun (source, column) =>
      (source.selector, SelCompress.mk column 1 1)) ++
    (combinations.zipIdx.flatMap fun (combination, column) =>
      combination.zipIdx.map fun (source, position) =>
        (source.selector, SelCompress.mk (degreeZero.length + column) combination.length (position + 1))) at hentry
  rcases List.mem_append.mp hentry with hzero | hcombined
  · obtain ⟨⟨source, column⟩, hindexed, rfl⟩ := List.mem_map.mp hzero
    have hsource := List.fst_mem_of_mem_zipIdx hindexed
    have hzero : source.maxDegree = 0 := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hsource).2
    exact ⟨source, (List.mem_filter.mp hsource).1, rfl, by simp [hzero]⟩
  · obtain ⟨⟨combination, column⟩, hcombination, hentry⟩ := List.mem_flatMap.mp hcombined
    obtain ⟨⟨source, position⟩, hsource, rfl⟩ := List.mem_map.mp hentry
    have hcombination := List.fst_mem_of_mem_zipIdx hcombination
    have hsource := List.fst_mem_of_mem_zipIdx hsource
    have hinRemaining : source ∈ remaining :=
      List.forall_iff_forall_mem.mp
        (forall_of_mem_buildCombinations budget remaining.length remaining combination
          (· ∈ remaining) (List.forall_iff_forall_mem.mpr fun _ h => h) hcombination) source hsource
    have hsourceAll : source ∈ selectors := (List.mem_filter.mp hinRemaining).1
    have hnonzero : source.maxDegree ≠ 0 := by
      simpa only [remaining, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hinRemaining).2
    have hremaining : remaining.Forall fun selected => selected.maxDegree ≤ budget :=
      List.forall_iff_forall_mem.mpr fun selected hselected =>
        List.forall_iff_forall_mem.mp hdegrees selected (List.mem_filter.mp hselected).1
    refine ⟨source, hsourceAll, rfl, ?_⟩
    simp only [hnonzero, ↓reduceIte]
    exact buildCombinations_degree_budget budget remaining.length hpositive remaining combination
      hremaining hcombination source hsource

/-- The largest replacement degree allowed by an original selector degree; degree-zero selectors stay singleton. -/
def selectorCompressionDegreeBudget (budget original : ℕ) : ℕ :=
  if original = 0 then 1 else budget + 1 - original

/-- The full compiler map respects its source degrees and emits valid root indices, for every activation pattern. -/
theorem deriveSelCompressMap_lookup_degree_budget {F : Type}
    (cs : ConstraintSystem F) (rows : ℕ) (activations : List (ℕ × ℕ))
    (hpositive : 1 ≤ csDegree cs)
    (hdegrees : ∀ selector < cs.numSelectors, (selectorMaxDegrees cs)[selector]! ≤ csDegree cs)
    (selector : ℕ) (compressed : SelCompress)
    (hlookup : (deriveSelCompressMap cs rows activations).lookup selector = some compressed) :
    1 ≤ compressed.assignedRoot ∧ compressed.assignedRoot ≤ compressed.combinationLen ∧
      compressed.combinationLen ≤ selectorCompressionDegreeBudget (csDegree cs)
        (selectorMaxDegrees cs)[selector]! := by
  let descriptions := (List.range cs.numSelectors).map fun i =>
    SelectorDescription.mk i (activationTable rows cs.numSelectors activations)[i]!
      (selectorMaxDegrees cs)[i]!
  have hdescriptionDegrees : descriptions.Forall fun source => source.maxDegree ≤ csDegree cs := by
    rw [List.forall_iff_forall_mem]
    intro source hsource
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hsource
    exact hdegrees i (List.mem_range.mp hi)
  have hmapped := SelCompressMap.mem_entries_of_lookup _ hlookup
  change (selector, compressed) ∈ (process descriptions (csDegree cs)).entries.map
    (fun entry => (entry.1, { entry.2 with packedCol := entry.2.packedCol + cs.numFixedColumns })) at hmapped
  obtain ⟨entry, hprocess, hequal⟩ := List.mem_map.mp hmapped
  have hselector := congrArg Prod.fst hequal
  have hcompressed := congrArg Prod.snd hequal
  change entry.1 = selector at hselector
  change { entry.2 with packedCol := entry.2.packedCol + cs.numFixedColumns } = compressed at hcompressed
  subst selector
  subst compressed
  have hroots := process_entry_root_degree_bounds descriptions (csDegree cs) hpositive entry hprocess
  refine ⟨hroots.1, hroots.2.1, ?_⟩
  obtain ⟨source, hsource, hselector, hbudget⟩ :=
    process_entry_degree_budget descriptions (csDegree cs) hpositive hdescriptionDegrees entry hprocess
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hsource
  change i = entry.1 at hselector
  change (if (selectorMaxDegrees cs)[i]! = 0 then entry.2.combinationLen = 1
    else (selectorMaxDegrees cs)[i]! - 1 + entry.2.combinationLen ≤ csDegree cs) at hbudget
  change entry.2.combinationLen ≤ selectorCompressionDegreeBudget (csDegree cs)
    (selectorMaxDegrees cs)[entry.1]!
  rw [← hselector]
  unfold selectorCompressionDegreeBudget
  split
  · simp_all
  · split at hbudget
    · contradiction
    · omega

end Zcash.Snark.ZeroKnowledge
