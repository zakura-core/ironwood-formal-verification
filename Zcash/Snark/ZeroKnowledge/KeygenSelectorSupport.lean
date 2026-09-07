import Clean.Halo2.TopLevel

/-!
# Packed selector columns end with the circuit placement

Loaded tables may continue through the whole usable prefix. The compiler's packed
selector columns have a stricter support bound: only selector activations write to
them, and every activation lies within V1 placement. Their rows are therefore zero
from the placement endpoint onward, including any unused part of the usable prefix.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

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

end Zcash.Snark.ZeroKnowledge
