import Zcash.Snark.ZeroKnowledge.StoredColumnSequenceCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic

/-- A counted sequence consumes exactly the reference row tape and preserves every earlier masked column. -/
theorem storedColumnRowsFromTapeCosted_result {Id : Type*} (width read : ℕ)
    (construct : Id → List (List Fp) → List Fp × ℕ)
    (source : Id → ColumnHistory width → Fin width → Fp)
    (hconstruct : ∀ id history, (construct id history).1 = List.ofFn (source id (storedColumnHistory width history)))
    (recipes : List (Id × ℕ)) (history : List (List Fp)) (tape : ℕ → Fp × ℕ) (offset : ℕ) :
    (storedColumnRowsFromTapeCosted width read construct recipes history tape offset).1 =
      (columnRowsFromTape (recipes.map (fun recipe => (⟨recipe.2, source recipe.1⟩ : ColumnStep width)))
        (storedColumnHistory width history) (fun index => (tape (offset + index.val)).1)).map List.ofFn := by
  induction recipes generalizing history offset with
  | nil => rfl
  | cons recipe rest ih =>
      let first : ColumnStep width := ⟨recipe.2, source recipe.1⟩
      let coins := fun index : Fin (width - recipe.2) => (tape (offset + index.val)).1
      let row := columnRowsFromCoins first (storedColumnHistory width history) coins
      let masked := storedMaskedRowsCosted read recipe.2 width (construct recipe.1 history)
        (fun index => ((tape (offset + index.val)).1, (tape (offset + index.val)).2 + 2))
      have hm : masked.1 = List.ofFn row := by
        simp only [masked, storedMaskedRowsCosted_result, hconstruct, storedRow_getD_ofFn]
        rfl
      have hh : storedColumnHistory width (masked.1 :: history) =
          row :: storedColumnHistory width history := by
        rw [hm, storedColumnHistory_cons_materialized]
      change masked.1 :: (storedColumnRowsFromTapeCosted width read construct rest
          (masked.1 :: history) tape (offset + (width - recipe.2))).1 =
        (columnRowsFromTape (first :: rest.map (fun recipe => (⟨recipe.2, source recipe.1⟩ : ColumnStep width)))
          (storedColumnHistory width history) (fun index => (tape (offset + index.val)).1)).map List.ofFn
      rw [ih, hh, hm]
      change List.ofFn row ::
          (columnRowsFromTape (rest.map (fun recipe => (⟨recipe.2, source recipe.1⟩ : ColumnStep width)))
            (row :: storedColumnHistory width history)
            (fun index => (tape (offset + (width - recipe.2) + index.val)).1)).map List.ofFn =
        List.ofFn row ::
          (columnRowsFromTape (rest.map (fun recipe => (⟨recipe.2, source recipe.1⟩ : ColumnStep width)))
            (row :: storedColumnHistory width history)
            (fun index => (tape (offset + ((width - recipe.2) + index.val))).1)).map List.ofFn
      simp only [Nat.add_assoc]

end Zcash.Snark.ZeroKnowledge
