import Zcash.Snark.ZeroKnowledge.ColumnSequence

/-!
# Retained rows of a total sequential construction

Each emitted column retains its constructor's prefix, evaluated on the exact earlier
masked history. This applies to the total comparison computation even when a partial
lookup construction would have failed; later failure cannot change earlier advice.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- A selected suffix tape leaves every earlier row of the current constructor unchanged. -/
theorem columnRowsFromCoins_retained {n : ℕ} (step : ColumnStep n) (history : ColumnHistory n)
    (tape : Fin (n - step.firstMasked) → Fp) (i : Fin n) (hi : i.val < step.firstMasked) :
    columnRowsFromCoins step history tape i = step.rows history i := by
  exact maskedRows_before _ _ i hi

/-- Every total output column retains its computed prefix on the actual preceding masked history. -/
theorem columnRowsFromTape_retained {n : ℕ} (steps : List (ColumnStep n))
    (history : ColumnHistory n) (tape : Fin (columnRowSampleCount steps) → Fp)
    (j : ℕ) (hj : j < steps.length) (i : Fin n) (hi : i.val < (steps[j]'hj).firstMasked) :
    ((columnRowsFromTape steps history tape).getD j 0) i =
      (steps[j]'hj).rows (((columnRowsFromTape steps history tape).take j).reverse ++ history) i := by
  induction steps generalizing history j with
  | nil => simp at hj
  | cons step rest ih =>
    let coins := splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest) Fp tape
    let row := columnRowsFromCoins step history coins.1
    cases j with
    | zero =>
      simpa only [columnRowsFromTape, List.getD_cons_zero, List.getElem_cons_zero,
        List.take_zero, List.reverse_nil, List.nil_append] using
        columnRowsFromCoins_retained step history coins.1 i hi
    | succ j =>
      have hj' : j < rest.length := Nat.lt_of_succ_lt_succ hj
      simpa only [columnRowsFromTape, List.getD_cons_succ, List.getElem_cons_succ,
        List.take_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (row :: history) coins.2 j hj' hi

end Zcash.Snark.ZeroKnowledge
