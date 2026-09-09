import Zcash.Snark.ZeroKnowledge.StoredRowMaskCost
import Zcash.Snark.ZeroKnowledge.ColumnSequence

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic

/-- Decode stored column rows using the reference zero default for missing entries. -/
def storedColumnHistory (width : ℕ) (history : List (List Fp)) : ColumnHistory width :=
  history.map fun values row => values.getD row.val 0

/-- Reading a valid index from a materialized row gives the original field value. -/
theorem storedRow_getD_ofFn {width : ℕ} (rows : Fin width → Fp) (row : Fin width) :
    (List.ofFn rows).getD row.val 0 = rows row := by
  simpa only [getDListCosted_result] using getDListCosted_ofFn_result 0 (0 : Fp) rows row

/-- Materialized source columns decode to exactly their original row functions. -/
theorem storedColumnHistory_materialize {width : ℕ} (history : ColumnHistory width) :
    storedColumnHistory width (history.map List.ofFn) = history := by
  simp only [storedColumnHistory, List.map_map, Function.comp_def, storedRow_getD_ofFn, List.map_id']

/-- Appending one materialized column preserves the full earlier decoded history. -/
theorem storedColumnHistory_cons_materialized {width : ℕ}
    (rows : Fin width → Fp) (history : List (List Fp)) :
    storedColumnHistory width (List.ofFn rows :: history) = rows :: storedColumnHistory width history := by
  simp only [storedColumnHistory, List.map_cons, storedRow_getD_ofFn]

/-- Execute an ordered stored-column recipe list, preserving every suffix offset and full masked history. -/
def storedColumnRowsFromTapeCosted {Id : Type*} (width read : ℕ)
    (construct : Id → List (List Fp) → List Fp × ℕ) :
    List (Id × ℕ) → List (List Fp) → (ℕ → Fp × ℕ) → ℕ → List (List Fp) × ℕ
  | [], _, _, _ => ([], 1)
  | recipe :: rest, history, tape, offset =>
      let base := construct recipe.1 history
      let masked := storedMaskedRowsCosted read recipe.2 width base (fun index =>
        let value := tape (offset + index.val)
        (value.1, value.2 + 2))
      let later := storedColumnRowsFromTapeCosted width read construct rest (masked.1 :: history)
        tape (offset + (width - recipe.2))
      (masked.1 :: later.1, masked.2 + later.2 + 4)

/-- The sequence materializes exactly one new column per recipe. -/
theorem storedColumnRowsFromTapeCosted_length {Id : Type*} (width read : ℕ)
    (construct : Id → List (List Fp) → List Fp × ℕ) (recipes : List (Id × ℕ))
    (history : List (List Fp)) (tape : ℕ → Fp × ℕ) (offset : ℕ) :
    (storedColumnRowsFromTapeCosted width read construct recipes history tape offset).1.length = recipes.length := by
  induction recipes generalizing history offset with
  | nil => rfl
  | cons recipe rest ih => simp only [storedColumnRowsFromTapeCosted, List.length_cons, ih]

/-- Every new stored column has the complete width, regardless of its constructor or masking boundary. -/
theorem storedColumnRowsFromTapeCosted_width {Id : Type*} (width read : ℕ)
    (construct : Id → List (List Fp) → List Fp × ℕ) (recipes : List (Id × ℕ))
    (history : List (List Fp)) (tape : ℕ → Fp × ℕ) (offset : ℕ) :
    ∀ values ∈ (storedColumnRowsFromTapeCosted width read construct recipes history tape offset).1,
      values.length = width := by
  induction recipes generalizing history offset with
  | nil => simp only [storedColumnRowsFromTapeCosted, List.not_mem_nil, false_implies, implies_true]
  | cons recipe rest ih =>
      intro values hvalues
      simp only [storedColumnRowsFromTapeCosted, List.mem_cons] at hvalues
      rcases hvalues with rfl | hvalues
      · exact storedMaskedRowsCosted_length _ _ _ _ _
      · exact ih _ _ values hvalues

end Zcash.Snark.ZeroKnowledge
