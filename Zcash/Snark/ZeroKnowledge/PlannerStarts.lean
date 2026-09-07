import Clean.Halo2.Keygen.PlannerTrace

/-!
# Exact start rows from compact planner certificates

A lawful planner trace already certifies each block's least fitting row and free
consecutive run. These lemmas recover every individual start, preserving the full
allocation transition needed to compose the blocks.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner Halo2.FloorPlanner.V1

/-- The consecutive start rows specified by a repeated region block. -/
def plannerRunStarts : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | count + 1, start, height => start :: plannerRunStarts count (start + height) height

/-- A certified free run gives every repeated region's exact start and the resulting allocation view. -/
theorem slotShapeSummariesFrom_replicate_starts
    (count : ℕ) (summary : RegionShapeSummary)
    (allocations : CircuitAllocations) (view : AllocationView) (start : ℕ)
    (hrepresents : view.Represents allocations) (hvalid : view.Valid)
    (hnodup : summary.columns.Nodup) (hcolumns : summary.columns ≠ [])
    (hlength : 0 < summary.rowCount)
    (hleast : view.LeastFit (sortRegionColumns summary.columns) summary.rowCount start)
    (hfree : view.FitsColumns (sortRegionColumns summary.columns) start
      ((count + 1) * summary.rowCount)) :
    let result := slotShapeSummariesFrom (List.replicate (count + 1) summary) allocations
    result.1 = plannerRunStarts (count + 1) start summary.rowCount ∧
      (view.insertRepeated (sortRegionColumns summary.columns) start
        summary.rowCount (count + 1)).Represents result.2 := by
  induction count generalizing allocations view start with
  | zero =>
      obtain ⟨updated, hplaced, hupdatedRepresents⟩ :=
        view.placeSummary_eq_of_leastFit summary allocations start
          hrepresents hvalid hnodup hlength hleast
      simp only [List.replicate_succ, List.replicate_zero, slotShapeSummariesFrom,
        hplaced, Option.getD_some, plannerRunStarts, AllocationView.insertRepeated]
      exact ⟨trivial, hupdatedRepresents⟩
  | succ count ih =>
      let columns := sortRegionColumns summary.columns
      have hsortedColumns : columns ≠ [] := by
        intro hempty
        have hlengths := (sortRegionColumns_perm summary.columns).length_eq
        have : summary.columns.length = 0 := by
          simpa [columns, hempty] using hlengths.symm
        exact hcolumns (List.eq_nil_of_length_eq_zero this)
      obtain ⟨updated, hplaced, hupdatedRepresents⟩ :=
        view.placeSummary_eq_of_leastFit summary allocations start
          hrepresents hvalid hnodup hlength hleast
      have hupdatedValid : (view.insert columns start summary.rowCount).Valid := by
        have hactual := placeSummary_valid summary allocations
          (hrepresents.valid hvalid) ⟨hnodup, fun _ => hlength⟩
        rw [hplaced] at hactual
        intro column
        rw [← hupdatedRepresents column]
        exact hactual column
      have hnextLeast := view.leastFit_insert_next hsortedColumns hlength hleast hfree
      have htailFree := view.fitsColumns_insert_tail hfree
      have hrecursive := ih updated (view.insert columns start summary.rowCount)
        (start + summary.rowCount) hupdatedRepresents hupdatedValid hnextLeast htailFree
      simp only [List.replicate_succ, slotShapeSummariesFrom, hplaced, Option.getD_some,
        plannerRunStarts, AllocationView.insertRepeated]
      exact ⟨congrArg (List.cons start) hrecursive.1, hrecursive.2⟩

/-- Expand the individual start rows of a compact planner trace. -/
def plannerTraceStarts (trace : List PlannedSummaryBlock) : List ℕ :=
  trace.flatMap fun block => plannerRunStarts block.count block.start block.summary.rowCount

/-- A lawful compact trace determines all start rows, as well as its final allocation view. -/
theorem slotShapeSummariesFrom_trace_starts
    (trace : List PlannedSummaryBlock) (allocations : CircuitAllocations) (view : AllocationView)
    (hrepresents : view.Represents allocations) (hvalid : view.Valid)
    (hlawful : PlannedSummaryBlock.Lawful view trace) :
    let result := slotShapeSummariesFrom (PlannedSummaryBlock.summaries trace) allocations
    result.1 = plannerTraceStarts trace ∧
      (PlannedSummaryBlock.finalView view trace).Represents result.2 := by
  induction trace generalizing allocations view with
  | nil => exact ⟨rfl, hrepresents⟩
  | cons block rest ih =>
      rcases block with ⟨blockCount, summary, start⟩
      rcases hlawful with ⟨hcount, hwellFormed, hcolumns, hleast, hfits, hrest⟩
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcount)
      let first := slotShapeSummariesFrom (List.replicate (count + 1) summary) allocations
      have hfirst := slotShapeSummariesFrom_replicate_starts count summary allocations view start
        hrepresents hvalid hwellFormed.1 hcolumns (hwellFormed.2 hcolumns) hleast hfits
      have hnextValid := view.insertRepeated_valid count hvalid hfits (hwellFormed.2 hcolumns)
      have htail := ih first.2
        (view.insertRepeated (sortRegionColumns summary.columns) start summary.rowCount (count + 1))
        hfirst.2 hnextValid hrest
      simp only [PlannedSummaryBlock.summaries, PlannedSummaryBlock.blocks, List.map_cons,
        List.flatMap_cons, slotShapeSummariesFrom_append,
        plannerTraceStarts, PlannedSummaryBlock.finalView]
      exact ⟨congrArg₂ List.append hfirst.1 htail.1, htail.2⟩

/-- Empty regions retain their zero starts and leave all allocations unchanged. -/
theorem slotShapeSummariesFrom_replicate_empty_starts
    (count : ℕ) (allocations : CircuitAllocations) :
    slotShapeSummariesFrom (List.replicate count { columns := [], rowCount := 0 }) allocations =
      (List.replicate count 0, allocations) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ, slotShapeSummariesFrom, placeSummary, sortRegionColumns,
        firstFit] using congrArg (fun result : List ℕ × CircuitAllocations =>
          (0 :: result.1, result.2)) ih

end Zcash.Snark.ZeroKnowledge
