import Zcash.Snark.ZeroKnowledge.PrivateColumnRoutingCost
import Zcash.Snark.ZeroKnowledge.ListCollectedCost

/-!
# Concrete readers for stored row matrices

Rows and entries are materialized lists. Both levels of lookup pay for actual
list traversal and preserve the original defaults. Function-valued observation
readers retain the full cost of each eventual lookup into their captured row.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Reading a materialized finite vector recovers its original valid entry. -/
theorem getDListCosted_ofFn_result {α : Type*} {count : ℕ} (read : ℕ) (fallback : α)
    (values : Fin count → α) (index : Fin count) :
    (getDListCosted read fallback (List.ofFn values) index.val).1 = values index := by
  have hi : index.val < (List.ofFn values).length := by
    simpa only [List.length_ofFn] using index.isLt
  simp only [getDListCosted_result, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

/-- Read a stored row and then its selected entry, retaining both traversals. -/
def storedMatrixEntryCosted {α : Type*} (read : ℕ) (fallback : α)
    (rows : List (List α)) (row column : ℕ) : α × ℕ :=
  let selected := getDListCosted read [] rows row
  let value := getDListCosted read fallback selected.1 column
  (value.1, selected.2 + value.2 + 1)

/-- The concrete matrix reader preserves both original list defaults. -/
theorem storedMatrixEntryCosted_result {α : Type*} (read : ℕ) (fallback : α)
    (rows : List (List α)) (row column : ℕ) :
    (storedMatrixEntryCosted read fallback rows row column).1 =
      (rows.getD row []).getD column fallback := by
  simp only [storedMatrixEntryCosted, getDListCosted_result]

/-- Matrix access is bounded by the stored row count and maximum stored row length. -/
theorem storedMatrixEntryCosted_cost_le {α : Type*} (read : ℕ) (fallback : α)
    (rows : List (List α)) (row column width : ℕ)
    (hrows : ∀ values ∈ rows, values.length ≤ width) :
    (storedMatrixEntryCosted read fallback rows row column).2 ≤
      2 * rows.length + 2 * width + 2 * read + 3 := by
  have hselected := getDListCosted_cost_le read [] rows row
  have hwidth := getDListCosted_property read [] rows (fun values => values.length ≤ width)
    (by simp) hrows row
  have hvalue := getDListCosted_cost_le read fallback (getDListCosted read [] rows row).1 column
  simp only [storedMatrixEntryCosted]
  omega

/-- Materializing a finite row family and reading its valid indices recovers that exact family. -/
theorem storedMatrixEntryCosted_ofFn {α : Type*} (read : ℕ) (fallback : α) {height width : ℕ}
    (rows : Fin height → Fin width → α) (row : Fin height) (column : Fin width) :
    (storedMatrixEntryCosted read fallback (List.ofFn (fun index => List.ofFn (rows index)))
      row.val column.val).1 = rows row column := by
  have hr : row.val < (List.ofFn (fun index => List.ofFn (rows index))).length := by
    simpa only [List.length_ofFn] using row.isLt
  have hc : column.val < (List.ofFn (rows row)).length := by
    simpa only [List.length_ofFn] using column.isLt
  simp only [storedMatrixEntryCosted_result, List.getD_eq_getElem _ _ hr, List.getElem_ofFn,
    List.getD_eq_getElem _ _ hc]

/-- Build finite-index readers for already stored rows; each later field read retains its traversal cost. -/
def storedRowReadersCosted {α : Type*} (read : ℕ) (fallback : α) (width : ℕ)
    (rows : List (List α)) : List (Fin width → α × ℕ) × ℕ :=
  mapListCosted (fun values => ((fun index : Fin width => getDListCosted read fallback values index.val), 2)) rows

/-- Reader construction captures precisely the original stored rows. -/
theorem storedRowReadersCosted_result {α : Type*} (read : ℕ) (fallback : α) (width : ℕ)
    (rows : List (List α)) :
    (storedRowReadersCosted read fallback width rows).1 =
      rows.map (fun values index => getDListCosted read fallback values index.val) := mapListCosted_result _ _

/-- The reader family contains exactly one reader for each stored row. -/
theorem storedRowReadersCosted_length {α : Type*} (read : ℕ) (fallback : α) (width : ℕ)
    (rows : List (List α)) : (storedRowReadersCosted read fallback width rows).1.length = rows.length := by
  simp only [storedRowReadersCosted_result, List.length_map]

/-- Reading materialized finite rows recovers the original entire row family. -/
theorem storedRowReadersCosted_erase_materialize {α : Type*} (read : ℕ) (fallback : α) {width : ℕ}
    (rows : List (Fin width → α)) :
    (storedRowReadersCosted read fallback width (rows.map List.ofFn)).1.map
      (fun reader index => (reader index).1) = rows := by
  simp only [storedRowReadersCosted_result, List.map_map, Function.comp_def,
    getDListCosted_ofFn_result, List.map_id']

/-- Constructing reader closures is linear; future field reads are charged separately. -/
theorem storedRowReadersCosted_cost_le {α : Type*} (read : ℕ) (fallback : α) (width : ℕ)
    (rows : List (List α)) :
    (storedRowReadersCosted read fallback width rows).2 ≤ rows.length * 3 + 1 := by
  exact mapListCosted_cost_le _ _ 2 (fun _ _ => le_rfl)

/-- Every generated reader has a concrete access bound from its stored row size. -/
theorem storedRowReadersCosted_readBound {α : Type*} (read : ℕ) (fallback : α) (width : ℕ)
    (rows : List (List α)) (bound : ℕ) (hrows : ∀ values ∈ rows, values.length ≤ bound)
    (reader : Fin width → α × ℕ) (hmem : reader ∈ (storedRowReadersCosted read fallback width rows).1)
    (index : Fin width) : (reader index).2 ≤ 2 * bound + read + 1 := by
  rw [storedRowReadersCosted_result, List.mem_map] at hmem
  obtain ⟨values, hvalues, rfl⟩ := hmem
  exact (getDListCosted_cost_le read fallback values index.val).trans (by have h := hrows values hvalues; omega)

end Zcash.Snark.ZeroKnowledge
