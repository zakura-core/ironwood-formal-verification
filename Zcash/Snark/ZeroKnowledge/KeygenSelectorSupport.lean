import Clean.Halo2.TopLevel

/-!
# Packed selector columns end with the circuit placement

Loaded tables may continue through the whole usable prefix. The compiler's packed
selector columns have a stricter support bound: only selector activations write to
them, and every activation lies within V1 placement. Their rows are therefore zero
from the placement endpoint onward, including any unused part of the usable prefix
and the row accessor's zero padding outside the compiler's dimensions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- A packed selector cell is zero when no activation at that row is routed to its column. -/
theorem topLevelSelectorRows_zero_of_no_activation {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) (column row : ℕ)
    (hselector : top.constraintSystem.numFixedColumns ≤ column)
    (hno : ∀ selector compressed,
      (selector, row) ∈ top.selectorActivations →
      top.selectorMap.lookup selector = some compressed → compressed.packedCol ≠ column) :
    (top.fixedRows.getD column []).getD row 0 = 0 := by
  by_cases hcolumn : column < top.fixedColumnCount
  · by_cases hrow : row < top.n
    · apply top.fixedRows_getD_getD_eq_zero_of_not_mem column row _ hcolumn hrow
      intro hcell
      obtain ⟨assignment, hassignment, hcell⟩ := List.mem_map.mp hcell
      obtain ⟨raw, hraw, hrawCell⟩ := List.mem_map.mp
        (top.fixedAssignment_cell_mem_raw_of_mem assignment hassignment)
      have hcolumnEq := congrArg Prod.fst (hrawCell.trans hcell)
      have hrowEq := congrArg Prod.snd (hrawCell.trans hcell)
      change raw.1 = column at hcolumnEq
      change raw.2.1 = row at hrowEq
      obtain ⟨selector, activationRow, compressed, hactivation, hlookup, rfl⟩ :=
        Layout.exists_selectorActivation_of_mem_rawAssignments_of_column_ge
          (top.usableRowsAt top.domainExponent) top.selectorMap top.constraintSystem top.operations
          top.keygenCoherent
          (by
            rw [List.forall_iff_forall_mem]
            intro constant hconstant
            exact top.constantColumn_index_lt_numFixedColumns hconstant)
          hraw (by simpa only [hcolumnEq] using hselector)
      exact hno selector compressed (hrowEq ▸ hactivation) hlookup hcolumnEq
    · apply List.getD_eq_default
      rw [top.fixedRows_getD_length column hcolumn]
      exact Nat.le_of_not_gt hrow
  · rw [List.getD_eq_default top.fixedRows [] (by
      rw [top.fixedRows_length]
      exact Nat.le_of_not_gt hcolumn)]
    rfl

/-- A raw write to a packed selector column comes from an activation before the placement endpoint. -/
theorem topLevelRawSelector_row_lt_placementEnd {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) (assignment : Layout.FixedAssignment F)
    (hassignment : assignment ∈ Layout.rawAssignments
      (top.usableRowsAt top.domainExponent) top.selectorMap top.constraintSystem top.operations)
    (hcolumn : top.constraintSystem.numFixedColumns ≤ assignment.1) :
    assignment.2.1 < FloorPlanner.V1.placementEnd top.operations := by
  obtain ⟨selector, row, compressed, hactivation, _, rfl⟩ :=
    Layout.exists_selectorActivation_of_mem_rawAssignments_of_column_ge
      (top.usableRowsAt top.domainExponent) top.selectorMap top.constraintSystem top.operations
      top.keygenCoherent
      (by
        rw [List.forall_iff_forall_mem]
        intro column hcolumn
        exact top.constantColumn_index_lt_numFixedColumns hcolumn)
      hassignment hcolumn
  exact FloorPlanner.V1.activation_row_lt_placementEnd top.operations hactivation

/-- The compiler's packed selector columns are zero from the placement endpoint onward. -/
theorem topLevelSelectorRows_zero_of_placementEnd_le {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) (column row : ℕ)
    (hselector : top.constraintSystem.numFixedColumns ≤ column)
    (hcolumn : column < top.fixedColumnCount) (hrow : row < top.n)
    (hafter : FloorPlanner.V1.placementEnd top.operations ≤ row) :
    (top.fixedRows.getD column []).getD row 0 = 0 := by
  apply top.fixedRows_getD_getD_eq_zero_of_not_mem column row _ hcolumn hrow
  intro hcell
  obtain ⟨assignment, hassignment, hcell⟩ := List.mem_map.mp hcell
  obtain ⟨raw, hraw, hrawCell⟩ := List.mem_map.mp
    (top.fixedAssignment_cell_mem_raw_of_mem assignment hassignment)
  have hcolumnEq := congrArg Prod.fst (hrawCell.trans hcell)
  have hrowEq := congrArg Prod.snd (hrawCell.trans hcell)
  change raw.1 = column at hcolumnEq
  change raw.2.1 = row at hrowEq
  have hbound := topLevelRawSelector_row_lt_placementEnd top raw hraw
    (by simpa only [hcolumnEq] using hselector)
  exact Nat.not_lt_of_ge hafter (hrowEq ▸ hbound)

/-- Selector rows stay zero after placement, including the accessor's zero padding outside its dimensions. -/
theorem topLevelSelectorRows_zero_after_placement {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) (column row : ℕ)
    (hselector : top.constraintSystem.numFixedColumns ≤ column)
    (hafter : FloorPlanner.V1.placementEnd top.operations ≤ row) :
    (top.fixedRows.getD column []).getD row 0 = 0 := by
  by_cases hcolumn : column < top.fixedColumnCount
  · by_cases hrow : row < top.n
    · exact topLevelSelectorRows_zero_of_placementEnd_le top column row hselector hcolumn hrow hafter
    · apply List.getD_eq_default
      rw [top.fixedRows_getD_length column hcolumn]
      exact Nat.le_of_not_gt hrow
  · rw [List.getD_eq_default top.fixedRows [] (by
      rw [top.fixedRows_length]
      exact Nat.le_of_not_gt hcolumn)]
    rfl

end Zcash.Snark.ZeroKnowledge
