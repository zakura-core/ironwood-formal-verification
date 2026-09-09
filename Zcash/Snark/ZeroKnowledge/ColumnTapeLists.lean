import Zcash.Snark.ZeroKnowledge.TapeList
import Mathlib.Data.List.GetD

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Separate the canonical interleaved tape by its declared tail lengths. -/
def columnTapeLists {n : ℕ} : List (ColumnStep n) → List Fp → List Fp × List Fp
  | [], _ => ([], [])
  | step :: rest, tape =>
    let count := n - step.firstMasked
    let later := columnTapeLists rest (tape.drop (count + 1))
    (tape.take count ++ later.1, tape.getD count 0 :: later.2)

/-- Consecutive canonical column blocks preserve both separated subsequences. -/
theorem columnTapeLists_append {n : ℕ} (first rest : List (ColumnStep n))
    (left right : List Fp) (hleft : left.length = columnFullSampleCount first) :
    columnTapeLists (first ++ rest) (left ++ right) =
      ((columnTapeLists first left).1 ++ (columnTapeLists rest right).1,
        (columnTapeLists first left).2 ++ (columnTapeLists rest right).2) := by
  induction first generalizing left with
  | nil =>
    have hz : left = [] := List.length_eq_zero_iff.mp hleft
    simp only [hz, columnTapeLists, List.nil_append]
  | cons step first ih =>
    have ht : n - step.firstMasked ≤ left.length := by
      simp only [columnFullSampleCount] at hleft
      omega
    have hb : n - step.firstMasked < left.length := by
      simp only [columnFullSampleCount] at hleft
      omega
    have hd : n - step.firstMasked + 1 ≤ left.length := by omega
    have hl : (left.drop (n - step.firstMasked + 1)).length = columnFullSampleCount first := by
      rw [List.length_drop, hleft]
      simp only [columnFullSampleCount]
      omega
    simp only [List.cons_append, columnTapeLists]
    rw [List.take_append_of_le_length ht, List.getD_append left right 0 _ hb,
      List.drop_append_of_le_length hd, ih _ hl]
    simp only [List.append_assoc]

/-- The list decoder agrees with the existing finite-tape equivalence on every complete tape. -/
theorem columnTapeLists_result {n : ℕ} (steps : List (ColumnStep n))
    (tape : Fin (columnFullSampleCount steps) → Fp) :
    columnTapeLists steps (List.ofFn tape) =
      (List.ofFn (columnCoinEquiv steps tape).1, List.ofFn (columnCoinEquiv steps tape).2) := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    rw [columnCoinEquiv_cons_lists]
    let first := splitTapeEquiv (n - step.firstMasked) (1 + columnFullSampleCount rest) Fp tape
    let next := splitTapeEquiv 1 (columnFullSampleCount rest) Fp first.2
    have hsplit : List.ofFn tape = List.ofFn first.1 ++ next.1 0 :: List.ofFn next.2 := by
      calc
        _ = List.ofFn first.1 ++ List.ofFn first.2 := ofFn_splitTape _ _ _ tape
        _ = _ := by
          rw [ofFn_splitTape Fp 1 (columnFullSampleCount rest) first.2]
          simp only [next, List.ofFn_succ, List.ofFn_zero, List.singleton_append]
    have hlength : (List.ofFn first.1).length = n - step.firstMasked := List.length_ofFn
    have ht : (List.ofFn first.1 ++ next.1 0 :: List.ofFn next.2).take (n - step.firstMasked) =
        List.ofFn first.1 := by
      exact List.take_left' hlength
    have hd : (List.ofFn first.1 ++ next.1 0 :: List.ofFn next.2).drop (n - step.firstMasked + 1) =
        List.ofFn next.2 := by
      have hh : (List.ofFn first.1 ++ next.1 0 :: List.ofFn next.2).drop (n - step.firstMasked) =
          next.1 0 :: List.ofFn next.2 := by
        simpa only [hlength] using (List.drop_append_length
          (l₁ := List.ofFn first.1) (l₂ := next.1 0 :: List.ofFn next.2))
      rw [← List.drop_drop, hh]
      rfl
    have hg : (List.ofFn first.1 ++ next.1 0 :: List.ofFn next.2).getD (n - step.firstMasked) 0 =
        next.1 0 := by
      rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self]
      rfl
    change columnTapeLists (step :: rest) (List.ofFn tape) =
      (List.ofFn first.1 ++ List.ofFn (columnCoinEquiv rest next.2).1,
        next.1 0 :: List.ofFn (columnCoinEquiv rest next.2).2)
    rw [hsplit]
    dsimp only [columnTapeLists]
    rw [ht, hd, hg, ih]

end Zcash.Snark.ZeroKnowledge
