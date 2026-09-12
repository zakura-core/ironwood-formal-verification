import Clean.Halo2.TopLevel

/-!
# Fixed columns vanish outside the usable rows

The circuit compiler writes tables only through the usable prefix. Region writes,
deferred constants, and packed selectors lie within the floor planner's placement.
Consequently the compiler's dense fixed columns are zero throughout the masking
suffix. This is a structural fact about the actual keygen functions; it does not
use a captured layout or a native decision certificate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- A table column fitting the usable rows assigns nothing beyond them, protecting masked boundary
rows. -/
private theorem tableColumnAssignment_row_lt {F : Type}
    (usable column : ℕ) (values : List F) (hvalues : values.length ≤ usable)
    {assignment : Layout.FixedAssignment F}
    (hassignment : assignment ∈ Layout.tableColumnAssignments usable column values) :
    assignment.2.1 < usable := by
  rcases values with _ | ⟨first, rest⟩
  · simp [Layout.tableColumnAssignments] at hassignment
  · simp only [Layout.tableColumnAssignments, List.mem_append] at hassignment
    rcases hassignment with hblock | hfill
    · obtain ⟨⟨value, row⟩, hrow, rfl⟩ := List.mem_map.mp hblock
      have := List.snd_lt_of_mem_zipIdx hrow
      change row < usable
      omega
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hfill
      have := List.mem_range.mp hrow
      change (first :: rest).length + row < usable
      omega

/-- Table loads fitting the usable rows stay within them, lifting the boundary-support result to
synthesis operations. -/
private theorem tableAssignment_row_lt {F : Type}
    (usable : ℕ) (operations : Operations F)
    (hloads : ∀ table values, .loadTable table values ∈ operations → values.length ≤ usable)
    {assignment : Layout.FixedAssignment F}
    (hassignment : assignment ∈ Layout.tableAssignments usable operations) :
    assignment.2.1 < usable := by
  induction operations with
  | nil => simp [Layout.tableAssignments] at hassignment
  | cons operation rest ih =>
      cases operation with
      | region name body | constrainInstance cell column row =>
          exact ih (fun table values hload => hloads table values (by simp [hload])) hassignment
      | loadTable table values =>
          simp only [Layout.tableAssignments, List.mem_append] at hassignment
          rcases hassignment with hcurrent | hrest
          · exact tableColumnAssignment_row_lt usable table.inner.index values
              (hloads table values (by simp)) hcurrent
          · exact ih (fun table values hload => hloads table values (by simp [hload])) hrest

/-- Every region fixed assignment precedes the placement end, connecting compiler layout to
fixed-column support. -/
private theorem regionAssignment_row_lt_placementEnd {F : Type}
    (operations : Operations F) {assignment : Layout.FixedAssignment F}
    (hassignment : assignment ∈
      Layout.regionAssignments (FloorPlanner.V1.starts operations) (indexedRegions operations 0).1) :
    assignment.2.1 < FloorPlanner.V1.placementEnd operations := by
  rw [Layout.regionAssignments, List.mem_flatMap] at hassignment
  obtain ⟨⟨index, body⟩, hregion, hbody⟩ := hassignment
  obtain ⟨operation, hoperation, hmapped⟩ := List.mem_filterMap.mp hbody
  cases operation with
  | assignFixed column row value =>
      simp only [Option.some.injEq] at hmapped
      subst assignment
      have hshape : FloorPlanner.measureRegion index body ∈ FloorPlanner.measureRegions operations :=
        List.mem_map.mpr ⟨(index, body), hregion, rfl⟩
      have hend := FloorPlanner.V1.shape_end_le_placementEndFrom_of_mem
        (FloorPlanner.measureRegions operations) (FloorPlanner.V1.starts operations)
        (FloorPlanner.measureRegion index body) hshape
      have hlocal : row < (FloorPlanner.measureRegion index body).rowCount := by
        have hbound := FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
          body (.assignFixed column row value) hoperation
        simpa only [FloorPlanner.measureRegion_rowCount, FloorPlanner.regionOperationRowExtent] using hbound
      exact (Nat.add_lt_add_left hlocal _).trans_le hend
  | assignAdvice | constrainEqual | constrainConstant | constrainInstance | enableGate | enableLookup =>
      simp at hmapped

/-- Every raw keygen fixed write is below the usable-row boundary. -/
theorem topLevelRawFixed_row_lt_usable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) (assignment : Layout.FixedAssignment F)
    (hassignment : assignment ∈ Layout.rawAssignments
      (top.usableRowsAt top.domainExponent) top.selectorMap top.constraintSystem top.operations) :
    assignment.2.1 < top.usableRowsAt top.domainExponent := by
  have hplacement : FloorPlanner.V1.placementEnd top.operations ≤ top.usableRowsAt top.domainExponent :=
    (Halo2.V1_placementEnd_le_usedRows top.operations).trans
      (top.operations_usedRows_le_usedRows.trans top.usedRows_le_usableRowsAt_domainExponent)
  simp only [Layout.rawAssignments, List.mem_append] at hassignment
  rcases hassignment with ((htable | hconstant) | hselector) | hregion
  · exact tableAssignment_row_lt _ top.operations
      (fun table values hload => (Operations.loadTable_length_le_usedRows top.operations table values hload).trans
        (top.operations_usedRows_le_usedRows.trans top.usedRows_le_usableRowsAt_domainExponent)) htable
  · obtain ⟨⟨value, column, row⟩, hsource, rfl⟩ := List.mem_map.mp hconstant
    exact (FloorPlanner.V1.constantAssignments_row_lt_placementEnd
      top.operations (top.constraintSystem.constants.map (·.index)) hsource).trans_le hplacement
  · obtain ⟨selector, row, compressed, hactivation, _, rfl⟩ :=
      Layout.exists_activation_lookup_of_mem_selectorAssignments _ _ hselector
    exact (FloorPlanner.V1.activation_row_lt_placementEnd top.operations hactivation).trans_le hplacement
  · exact (regionAssignment_row_lt_placementEnd top.operations hregion).trans_le hplacement

/-- Deduplication and sorting cannot introduce a fixed write in the masking suffix. -/
theorem topLevelFixed_row_lt_usable {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) (assignment : Layout.FixedAssignment F)
    (hassignment : assignment ∈ top.fixedAssignments) :
    assignment.2.1 < top.usableRowsAt top.domainExponent := by
  obtain ⟨raw, hraw, hcell⟩ := List.mem_map.mp
    (top.fixedAssignment_cell_mem_raw_of_mem assignment hassignment)
  have hrow := congrArg Prod.snd hcell
  change raw.2.1 = assignment.2.1 at hrow
  exact hrow ▸ topLevelRawFixed_row_lt_usable top raw hraw

/-- The actual dense fixed columns are zero on every masked domain row. -/
theorem topLevelFixedRows_zero_of_usable_le {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) (column row : ℕ)
    (hcolumn : column < top.fixedColumnCount) (hrow : row < top.n)
    (hmasked : top.usableRowsAt top.domainExponent ≤ row) :
    (top.fixedRows.getD column []).getD row 0 = 0 := by
  apply top.fixedRows_getD_getD_eq_zero_of_not_mem column row _ hcolumn hrow
  intro hcell
  obtain ⟨assignment, hassignment, hcell⟩ := List.mem_map.mp hcell
  have hbound := topLevelFixed_row_lt_usable top assignment hassignment
  have hrowEq := congrArg Prod.snd hcell
  change assignment.2.1 = row at hrowEq
  exact Nat.not_lt_of_ge hmasked (hrowEq ▸ hbound)

end Zcash.Snark.ZeroKnowledge
