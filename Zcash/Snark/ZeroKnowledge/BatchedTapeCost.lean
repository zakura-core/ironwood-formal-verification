import Zcash.Snark.ZeroKnowledge.TapeSplitCost
import Zcash.Snark.ZeroKnowledge.BatchedTapeLists

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Execute the batch decoder with counted metadata, tape traversal, and output construction. -/
def batchedColumnTapeListsCosted {n : ℕ} (read : ℕ) :
    List (List (ColumnStep n)) → List Fp → (List Fp × List Fp) × ℕ
  | [], _ => (([], []), 1)
  | block :: rest, tape =>
    let rowCount := columnRowSampleCountCosted block
    let blindCount := lengthListCosted block
    let first := splitListCosted read rowCount.1 tape
    let next := splitListCosted read blindCount.1 first.1.2
    let later := batchedColumnTapeListsCosted read rest next.1.2
    let rows := appendListCosted first.1.1 later.1.1
    let blinds := appendListCosted next.1.1 later.1.2
    ((rows.1, blinds.1), rowCount.2 + blindCount.2 + first.2 + next.2 + later.2 + rows.2 + blinds.2 + 8)

/-- Erasure retains the exact direct batch decoder on complete or truncated inputs. -/
theorem batchedColumnTapeListsCosted_result {n : ℕ} (read : ℕ)
    (batches : List (List (ColumnStep n))) (tape : List Fp) :
    (batchedColumnTapeListsCosted read batches tape).1 = batchedColumnTapeLists batches tape := by
  induction batches generalizing tape with
  | nil => rfl
  | cons block rest ih =>
    simp only [batchedColumnTapeListsCosted, appendListCosted_result, ih, splitListCosted_result,
      columnRowSampleCountCosted_result, lengthListCosted_result, batchedColumnTapeLists, List.drop_drop]

/-- The complete finite-tape law uses this same counted decoder. -/
theorem batchedColumnTapeListsCosted_source {n : ℕ} (read : ℕ)
    (batches : List (List (ColumnStep n))) (tape : Fin (batchedColumnSampleCount batches) → Fp) :
    (batchedColumnTapeListsCosted read batches (List.ofFn tape)).1 =
      (List.ofFn (columnCoinEquiv batches.flatten (batchedToColumnTape batches tape)).1,
        List.ofFn (columnCoinEquiv batches.flatten (batchedToColumnTape batches tape)).2) := by
  rw [batchedColumnTapeListsCosted_result, batchedColumnTapeLists_result]

/-- All decoder work is polynomial in the supplied batch and tape sizes, including short input. -/
theorem batchedColumnTapeListsCosted_cost_le {n : ℕ} (read : ℕ)
    (batches : List (List (ColumnStep n))) (tape : List Fp) (columns tapeSize : ℕ)
    (hblocks : ∀ block ∈ batches, block.length ≤ columns) (htape : tape.length ≤ tapeSize) :
    (batchedColumnTapeListsCosted read batches tape).2 ≤
      batches.length * (2 * tapeSize * (read + 3) + 4 * columns + 16) + 1 := by
  induction batches generalizing tape with
  | nil => simp [batchedColumnTapeListsCosted]
  | cons block rest ih =>
    let rowCount := columnRowSampleCountCosted block
    let blindCount := lengthListCosted block
    let first := splitListCosted read rowCount.1 tape
    let next := splitListCosted read blindCount.1 first.1.2
    let later := batchedColumnTapeListsCosted read rest next.1.2
    have hf := splitListCosted_lengths_le read rowCount.1 tape
    have hn := splitListCosted_lengths_le read blindCount.1 first.1.2
    have hfirst : first.2 ≤ tapeSize * (read + 2) + 1 :=
      (splitListCosted_cost_le read rowCount.1 tape).trans (by gcongr)
    have hnext : next.2 ≤ tapeSize * (read + 2) + 1 :=
      (splitListCosted_cost_le read blindCount.1 first.1.2).trans (by gcongr; exact hf.2.trans htape)
    have hlater := ih next.1.2 (fun entry he => hblocks entry (List.mem_cons_of_mem block he))
      (hn.2.trans (hf.2.trans htape))
    have hrows : (appendListCosted first.1.1 later.1.1).2 ≤ tapeSize + 1 := by
      rw [appendListCosted_cost]
      exact Nat.add_le_add_right (hf.1.trans htape) 1
    have hblinds : (appendListCosted next.1.1 later.1.2).2 ≤ tapeSize + 1 := by
      rw [appendListCosted_cost]
      exact Nat.add_le_add_right (hn.1.trans (hf.2.trans htape)) 1
    have hb := hblocks block (by simp)
    have hr : rowCount.2 = 3 * block.length + 1 := columnRowSampleCountCosted_cost block
    have hc : blindCount.2 = block.length + 1 := lengthListCosted_cost block
    change rowCount.2 + blindCount.2 + first.2 + next.2 + later.2 +
      (appendListCosted first.1.1 later.1.1).2 + (appendListCosted next.1.1 later.1.2).2 + 8 ≤ _
    rw [hr, hc, List.length_cons, Nat.add_mul, Nat.one_mul]
    nlinarith

end Zcash.Snark.ZeroKnowledge
