import Zcash.Snark.ZeroKnowledge.StoredColumnSequenceCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic

/-- Uniform sequence bound from materialized column, tape, and history bounds. -/
theorem storedColumnRowsFromTapeCosted_cost_le {Id : Type*} (width read : ℕ)
    (construct : Id → List (List Fp) → List Fp × ℕ)
    (recipes : List (Id × ℕ)) (history : List (List Fp)) (tape : ℕ → Fp × ℕ) (offset : ℕ)
    (limit columnBound tapeRead : ℕ)
    (hwidth : ∀ id earlier, (construct id earlier).1.length = width)
    (hconstruct : ∀ id earlier, earlier.length ≤ limit →
      (∀ values ∈ earlier, values.length ≤ width) → (construct id earlier).2 ≤ columnBound)
    (htape : ∀ index, (tape index).2 ≤ tapeRead)
    (hlength : history.length + recipes.length ≤ limit)
    (hhistory : ∀ values ∈ history, values.length ≤ width) :
    (storedColumnRowsFromTapeCosted width read construct recipes history tape offset).2 ≤
      recipes.length * (columnBound + width * (2 * width + read + tapeRead + 6) + width * width + 6) + 1 := by
  induction recipes generalizing history offset with
  | nil => simp only [storedColumnRowsFromTapeCosted, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons recipe rest ih =>
      let base := construct recipe.1 history
      let masked := storedMaskedRowsCosted read recipe.2 width base (fun index =>
        ((tape (offset + index.val)).1, (tape (offset + index.val)).2 + 2))
      have hb : base.2 ≤ columnBound := hconstruct recipe.1 history (by
        simp only [List.length_cons] at hlength
        omega) hhistory
      have hm := storedMaskedRowsCosted_cost_le read recipe.2 width base
        (fun index => ((tape (offset + index.val)).1, (tape (offset + index.val)).2 + 2))
        (tapeRead + 2) (fun index => Nat.add_le_add_right (htape (offset + index.val)) 2)
      have hbase : base.1.length = width := hwidth recipe.1 history
      rw [hbase] at hm
      rw [show 2 * width + read + (tapeRead + 2) + 4 =
        2 * width + read + tapeRead + 6 by omega] at hm
      have hmasked : masked.1.length = width := storedMaskedRowsCosted_length _ _ _ _ _
      have hnext : (masked.1 :: history).length + rest.length ≤ limit := by
        simp only [List.length_cons] at hlength ⊢
        omega
      have hrows : ∀ values ∈ masked.1 :: history, values.length ≤ width := by
        intro values hvalues
        rcases List.mem_cons.mp hvalues with rfl | hvalues
        · exact hmasked.le
        · exact hhistory values hvalues
      have hr := ih (masked.1 :: history) (offset + (width - recipe.2)) hnext hrows
      change masked.2 ≤ _ at hm
      change masked.2 + (storedColumnRowsFromTapeCosted width read construct rest
        (masked.1 :: history) tape (offset + (width - recipe.2))).2 + 4 ≤ _
      simp only [List.length_cons]
      nlinarith

end Zcash.Snark.ZeroKnowledge
