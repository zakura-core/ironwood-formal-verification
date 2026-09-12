import Zcash.Snark.ZeroKnowledge.SelectorPackingRoots
import Zcash.Snark.ZeroKnowledge.KeygenSelectorSupport
import Clean.Halo2.Keygen.Semantics

/-!
# Inactive selectors remain zero after compression

An active selector writes its assigned root to the packed fixed column. If a
different selector in that column is inactive, its replacement polynomial
vanishes at that root. If the entire column is inactive, it vanishes at zero.
The field-encoding premise is explicit: selector roots use `FiniteField.fromNat`,
which agrees with natural-number casts for the prime fields used by Ironwood.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- An actual selector activation determines the compiled packed-cell value. -/
theorem topLevelActiveSelector_fixedValue {F Config : Type} [FiniteField F]
    {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) {selector row : ℕ} {compressed : SelCompress}
    (hactivation : (selector, row) ∈ top.selectorActivations)
    (hlookup : top.selectorMap.lookup selector = some compressed) :
    (top.fixedRows.getD compressed.packedCol []).getD row 0 =
      FiniteField.fromNat compressed.assignedRoot := by
  apply top.fixedRows_getD_getD_eq_of_mem_raw
    (compressed.packedCol, row, FiniteField.fromNat compressed.assignedRoot)
  have hselector := Layout.mem_selectorAssignments_of_activation top.selectorMap
    top.selectorActivations hactivation hlookup (F := F)
  unfold Layout.rawAssignments
  exact List.mem_append_left _ (List.mem_append_right _ hselector)

/-- An inactive original selector has zero replacement value, regardless of which
other selector occupies its packed column. No concrete packing trace is assumed. -/
theorem topLevelSelectorReplacement_zero_of_inactive {F Config : Type} [FiniteField F]
    {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)
    (hcast : ∀ value : ℕ, (FiniteField.fromNat value : F) = (value : F))
    {selector row : ℕ} {compressed : SelCompress}
    (hlookup : top.selectorMap.lookup selector = some compressed)
    (hinactive : (selector, row) ∉ top.selectorActivations)
    (valuation : Query → F)
    (hvalue : valuation (.fixed ⟨compressed.packedCol⟩ 0) =
      (top.fixedRows.getD compressed.packedCol []).getD row 0) :
    (selReplacement compressed).eval valuation = 0 := by
  have hlookup' := hlookup
  rw [top.selectorMap_eq_derive] at hlookup'
  obtain ⟨column, _, hcolumn⟩ := deriveSelCompressMap_lookup_packedColumn
    top.constraintSystem top.n top.selectorActivations hlookup'
  by_cases hactive : ∃ active other,
      (active, row) ∈ top.selectorActivations ∧ top.selectorMap.lookup active = some other ∧
        other.packedCol = compressed.packedCol
  · obtain ⟨active, other, hactivation, hother, hsameColumn⟩ := hactive
    have hother' := hother
    rw [top.selectorMap_eq_derive] at hother'
    have hcoordinates := deriveSelCompressMap_lookup_root_coordinates
      top.constraintSystem top.n top.selectorActivations hlookup' hother' hsameColumn.symm
    apply selReplacement_eval_of_other compressed valuation other.assignedRoot
    · rw [hvalue]
      have hwritten := topLevelActiveSelector_fixedValue top hactivation hother
      rw [hsameColumn, hcast] at hwritten
      exact hwritten
    · exact hcoordinates.2.1
    · exact hcoordinates.2.2.1
    · intro hequal
      have hsource := hcoordinates.2.2.2 hequal.symm
      apply hinactive
      simpa only [hsource] using hactivation
  · apply selReplacement_eval_of_zero
    rw [hvalue]
    apply topLevelSelectorRows_zero_of_no_activation top compressed.packedCol row (by omega)
    intro active other hactivation hother hsameColumn
    exact hactive ⟨active, other, hactivation, hother, hsameColumn⟩

end Zcash.Snark.ZeroKnowledge
