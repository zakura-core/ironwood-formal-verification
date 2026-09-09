import Zcash.Snark.ZeroKnowledge.StoredRowsCost
import Zcash.Snark.ZeroKnowledge.RowMaskSampling

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic

/-- Apply the original increasing-row suffix tape to a stored column and materialize the masked result. -/
def storedMaskedRowsCosted (read firstMasked width : ℕ) (base : List Fp × ℕ)
    (tape : Fin (width - firstMasked) → Fp × ℕ) : List Fp × ℕ :=
  let values := ofFnCosted fun row : Fin width =>
    if h : firstMasked ≤ row.val then
      let value := tape ⟨row.val - firstMasked, by omega⟩
      (value.1, value.2 + 3)
    else
      let value := getDListCosted read 0 base.1 row.val
      (value.1, value.2 + 1)
  (values.1, base.2 + values.2 + 1)

/-- Every masked row consumes the original suffix index; earlier rows retain their stored value. -/
theorem storedMaskedRowsCosted_result (read firstMasked width : ℕ) (base : List Fp × ℕ)
    (tape : Fin (width - firstMasked) → Fp × ℕ) :
    (storedMaskedRowsCosted read firstMasked width base tape).1 =
      List.ofFn (maskedRows firstMasked (fun row : Fin width => base.1.getD row.val 0)
        (rowMaskTapeEquiv width firstMasked (fun index => (tape index).1))) := by
  simp only [storedMaskedRowsCosted, ofFnCosted_result]
  congr 1
  funext row
  by_cases h : firstMasked ≤ row.val <;>
    simp only [h, ↓reduceDIte, maskedRows, rowMaskTapeEquiv_apply, getDListCosted_result]

/-- Suffix masking always materializes the full column width. -/
theorem storedMaskedRowsCosted_length (read firstMasked width : ℕ) (base : List Fp × ℕ)
    (tape : Fin (width - firstMasked) → Fp × ℕ) :
    (storedMaskedRowsCosted read firstMasked width base tape).1.length = width := by
  rw [storedMaskedRowsCosted_result, List.length_ofFn]

/-- Complete mask cost includes base preparation, stored-prefix reads, suffix indexing, and all list cells. -/
theorem storedMaskedRowsCosted_cost_le (read firstMasked width : ℕ) (base : List Fp × ℕ)
    (tape : Fin (width - firstMasked) → Fp × ℕ) (tapeRead : ℕ)
    (htape : ∀ index, (tape index).2 ≤ tapeRead) :
    (storedMaskedRowsCosted read firstMasked width base tape).2 ≤
      base.2 + width * (2 * base.1.length + read + tapeRead + 4) + width * width + 2 := by
  let reader := fun row : Fin width =>
    if h : firstMasked ≤ row.val then
      let value := tape ⟨row.val - firstMasked, by omega⟩
      (value.1, value.2 + 3)
    else
      let value := getDListCosted read 0 base.1 row.val
      (value.1, value.2 + 1)
  have hr (row : Fin width) : (reader row).2 ≤ 2 * base.1.length + read + tapeRead + 3 := by
    dsimp only [reader]
    split
    · have h := htape ⟨row.val - firstMasked, by omega⟩
      omega
    · have h := getDListCosted_cost_le read (0 : Fp) base.1 row.val
      omega
  have h := ofFnCosted_cost_le reader _ hr
  rw [show 2 * base.1.length + read + tapeRead + 3 + 1 =
    2 * base.1.length + read + tapeRead + 4 by omega] at h
  change base.2 + (ofFnCosted reader).2 + 1 ≤ _
  omega

end Zcash.Snark.ZeroKnowledge
