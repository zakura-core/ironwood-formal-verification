import Zcash.Snark.ZeroKnowledge.KeygenSelectorSupport
import Zcash.Snark.ZeroKnowledge.SelectorPackingRoots
import Clean.Halo2.Keygen.Semantics

/-!
# Inactive selectors in the compiled fixed columns

For prime fields, an inactive source selector's replacement polynomial is zero
in the actual compiler rows. An occupied packed cell retains another selector's
root, which annihilates the replacement; an unoccupied cell is zero. The theorem
uses the compiler's source provenance and root-coordinate proofs for every row.

The prime-field restriction makes the compiler's natural-number embedding equal
to the scalar cast used by the root polynomial. No challenge or witness validity
premise is required.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- An inactive source selector has zero replacement in the actual compiled fixed rows. -/
theorem topLevel_selReplacement_zero_of_inactive {p : ℕ} [Fact p.Prime]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit (F p) Config PublicInput)
    (selector : ℕ) (compressed : SelCompress)
    (hlookup : top.selectorMap.lookup selector = some compressed)
    (row : ℕ) (hrow : row < top.n)
    (valuation : Query → F p)
    (hvalue : valuation (.fixed ⟨compressed.packedCol⟩ 0) =
      (top.fixedRows.getD compressed.packedCol []).getD row 0)
    (hinactive : (selector, row) ∉ top.selectorActivations) :
    (selReplacement compressed).eval valuation = 0 := by
  obtain ⟨index, hindex, hcolumn⟩ := deriveSelCompressMap_lookup_packedColumn
    top.constraintSystem top.n top.selectorActivations hlookup
  change index < top.selectorMap.newFixedCols at hindex
  have hprefix : top.constraintSystem.numFixedColumns ≤ compressed.packedCol := by omega
  have hbound : compressed.packedCol < top.fixedColumnCount := by
    rw [top.fixedColumnCount_eq]
    omega
  by_cases hcell : (compressed.packedCol, row) ∈ top.fixedAssignments.map Layout.FixedAssignment.cell
  · obtain ⟨assignment, hassignment, hcellEq⟩ := List.mem_map.mp hcell
    obtain ⟨raw, hraw, hrawCell⟩ := List.mem_map.mp
      (top.fixedAssignment_cell_mem_raw_of_mem assignment hassignment)
    have hcoordinates := hrawCell.trans hcellEq
    have hrawPrefix : top.constraintSystem.numFixedColumns ≤ raw.1 := by
      have h := congrArg Prod.fst hcoordinates
      exact h ▸ hprefix
    have hrawValue := top.fixedRows_getD_getD_eq_of_mem_raw raw hraw
    obtain ⟨other, otherRow, otherCompressed, hactivation, hother, rfl⟩ :=
      Layout.exists_selectorActivation_of_mem_rawAssignments_of_column_ge
        (top.usableRowsAt top.domainExponent) top.selectorMap top.constraintSystem top.operations
        top.keygenCoherent
        (by
          rw [List.forall_iff_forall_mem]
          intro constant hconstant
          exact top.constantColumn_index_lt_numFixedColumns hconstant)
        hraw hrawPrefix
    have hpacked : otherCompressed.packedCol = compressed.packedCol := congrArg Prod.fst hcoordinates
    have hrows : otherRow = row := congrArg Prod.snd hcoordinates
    subst otherRow
    have roots := deriveSelCompressMap_lookup_root_coordinates
      top.constraintSystem top.n top.selectorActivations hlookup hother hpacked.symm
    apply selReplacement_eval_of_other compressed valuation otherCompressed.assignedRoot
    · rw [hvalue, ← hpacked]
      simpa only [FiniteField.fromNat_F] using hrawValue
    · exact roots.2.1
    · exact roots.2.2.1
    · intro hequal
      have hselector : selector = other := roots.2.2.2 hequal.symm
      exact hinactive (hselector ▸ hactivation)
  · apply selReplacement_eval_of_zero compressed valuation
    exact hvalue.trans (top.fixedRows_getD_getD_eq_zero_of_not_mem
      compressed.packedCol row hcell hbound hrow)

end Zcash.Snark.ZeroKnowledge
