import Clean.Halo2.Keygen.CompressSelectors
import Init.Data.BitVec.Lemmas

/-!
# Bit-vector certificates for selector activation rows

The compiler stores one Boolean array per selector. A fixed-width bit vector
records exactly the same rows, including the behavior of duplicate activations
and out-of-bounds indices. The refinement supports finite packing certificates
without repeatedly normalizing the dense Boolean table.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Decode a row bit vector into the compiler's Boolean-array representation. -/
def selectorBitsRows {rows : ℕ} (bits : BitVec rows) : Array Bool :=
  Array.ofFn (fun row : Fin rows => bits.getLsbD row.val)

/-- Decoding retains the full domain width. -/
theorem selectorBitsRows_size {rows : ℕ} (bits : BitVec rows) :
    (selectorBitsRows bits).size = rows := by
  simp [selectorBitsRows]

/-- The zero bit vector is the compiler's initially inactive row array. -/
theorem selectorBitsRows_zero (rows : ℕ) :
    selectorBitsRows (0 : BitVec rows) = Array.replicate rows false := by
  apply Array.ext
  · simp [selectorBitsRows]
  · intro index hleft hright
    simp [selectorBitsRows]

/-- Setting one row bit is exactly the compiler's bounded Boolean-array update. -/
theorem selectorBitsRows_or_row {rows : ℕ} (bits : BitVec rows) (row : ℕ) :
    selectorBitsRows (bits ||| ((1 : BitVec rows) <<< row)) =
      (selectorBitsRows bits).set! row true := by
  apply Array.ext
  · simp [selectorBitsRows, Array.set!]
  · intro index hleft hright
    have hindex : index < rows := by simpa [selectorBitsRows] using hleft
    by_cases heq : row = index
    · subst row
      simp [selectorBitsRows, Array.set!]
    · by_cases hle : row ≤ index
      · have hsub : index - row ≠ 0 := by omega
        simp [selectorBitsRows, Array.set!, hindex, heq, hsub]
      · have hsmall : index < row := by omega
        simp [selectorBitsRows, Array.set!, hindex, heq, hsmall]

/-- The compiler's activation fold, storing each row array as a fixed-width bit vector. -/
def selectorActivationBits (rows selectors : ℕ) (activations : List (ℕ × ℕ)) :
    Array (BitVec rows) :=
  activations.foldl (fun table activation =>
    table.modify activation.1 (fun bits => bits ||| ((1 : BitVec rows) <<< activation.2)))
    (Array.replicate selectors 0)

/-- Updating activation bits preserves the number of allocated selectors. -/
theorem selectorActivationBits_size (rows selectors : ℕ) (activations : List (ℕ × ℕ)) :
    (selectorActivationBits rows selectors activations).size = selectors := by
  have hsize (table : Array (BitVec rows)) :
      (activations.foldl (fun current activation =>
        current.modify activation.1 (fun bits => bits ||| ((1 : BitVec rows) <<< activation.2)))
        table).size = table.size := by
    induction activations generalizing table with
    | nil => rfl
    | cons activation rest ih =>
        rw [List.foldl_cons, ih]
        simp
  simpa [selectorActivationBits] using hsize (Array.replicate selectors 0)

private theorem decode_modify {rows : ℕ} (table : Array (BitVec rows)) (selector row : ℕ) :
    (table.modify selector (fun bits => bits ||| ((1 : BitVec rows) <<< row))).map selectorBitsRows =
      (table.map selectorBitsRows).modify selector (fun values => values.set! row true) := by
  apply Array.ext
  · simp
  · intro index hleft hright
    by_cases heq : selector = index
    · subst index
      simp only [Array.getElem_map, Array.getElem_modify]
      exact selectorBitsRows_or_row _ row
    · simp [Array.getElem_modify, heq]

private theorem decode_fold {rows : ℕ} (table : Array (BitVec rows))
    (activations : List (ℕ × ℕ)) :
    (activations.foldl (fun current activation =>
      current.modify activation.1 (fun bits => bits ||| ((1 : BitVec rows) <<< activation.2)))
      table).map selectorBitsRows =
      activations.foldl (fun current activation =>
        current.modify activation.1 (fun values => values.set! activation.2 true))
        (table.map selectorBitsRows) := by
  induction activations generalizing table with
  | nil => rfl
  | cons activation rest ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, decode_modify]

/-- Decoding the bit-vector fold gives the actual compiler activation table exactly. -/
theorem activationTable_eq_selectorBitsRows (rows selectors : ℕ)
    (activations : List (ℕ × ℕ)) :
    activationTable rows selectors activations =
      (selectorActivationBits rows selectors activations).map selectorBitsRows := by
  unfold activationTable selectorActivationBits
  rw [decode_fold]
  simp only [Array.map_replicate, selectorBitsRows_zero]
  rfl

/-- Conflict testing on decoded row bits is exactly nonzero bitwise intersection. -/
theorem selectorBitsRows_conflicts {rows : ℕ} (left right : BitVec rows)
    (leftSelector rightSelector leftDegree rightDegree : ℕ) :
    (SelectorDescription.mk leftSelector (selectorBitsRows left) leftDegree).conflicts
        (SelectorDescription.mk rightSelector (selectorBitsRows right) rightDegree) =
      decide (left &&& right ≠ 0) := by
  have hexists :
      (SelectorDescription.mk leftSelector (selectorBitsRows left) leftDegree).conflicts
          (SelectorDescription.mk rightSelector (selectorBitsRows right) rightDegree) = true ↔
        ∃ row, row < rows ∧ left.getLsbD row = true ∧ right.getLsbD row = true := by
    constructor
    · intro hconflict
      rw [SelectorDescription.conflicts, List.any_eq_true] at hconflict
      obtain ⟨pair, hmember, hboth⟩ := hconflict
      obtain ⟨row, hrow, hvalue⟩ := List.mem_iff_getElem.mp hmember
      have hbound : row < rows := by simpa [selectorBitsRows] using hrow
      have hpair : (left.getLsbD row, right.getLsbD row) = pair := by
        simpa [selectorBitsRows] using hvalue
      have hbits := (congrArg (fun pair : Bool × Bool => pair.1 && pair.2) hpair).trans hboth
      have hparts : left.getLsbD row = true ∧ right.getLsbD row = true := by
        simpa only [Bool.and_eq_true] using hbits
      exact ⟨row, hbound, hparts⟩
    · rintro ⟨row, hrow, hleft, hright⟩
      exact SelectorDescription.conflicts_eq_true_of_activated
        (SelectorDescription.mk leftSelector (selectorBitsRows left) leftDegree)
        (SelectorDescription.mk rightSelector (selectorBitsRows right) rightDegree) row
        (by simpa [selectorBitsRows] using hrow) (by simpa [selectorBitsRows] using hrow)
        (by simpa [selectorBitsRows] using hleft) (by simpa [selectorBitsRows] using hright)
  have hbits : left &&& right ≠ 0 ↔
      ∃ row, row < rows ∧ left.getLsbD row = true ∧ right.getLsbD row = true := by
    simp only [ne_eq, BitVec.eq_of_getLsbD_eq_iff, BitVec.getLsbD_and]
    push Not
    simp
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using hexists.trans hbits.symm

end Zcash.Snark.ZeroKnowledge
