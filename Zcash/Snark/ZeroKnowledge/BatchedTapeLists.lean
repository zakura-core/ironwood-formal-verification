import Zcash.Snark.ZeroKnowledge.ColumnTapeLists

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Changing only a finite tape's length proof preserves its materialized values. -/
theorem ofFn_castTape {A : Type*} {m n : ℕ} (h : m = n) (tape : Fin m → A) :
    List.ofFn (Equiv.cast (congrArg (fun count => Fin count → A) h) tape) = List.ofFn tape := by
  subst n
  rfl

/-- Batch conversion concatenates the converted blocks without changing their order. -/
theorem batchedToColumnTape_cons_list {n : ℕ} (block : List (ColumnStep n))
    (rest : List (List (ColumnStep n)))
    (tape : Fin (batchedColumnSampleCount (block :: rest)) → Fp) :
    List.ofFn (batchedToColumnTape (block :: rest) tape) =
      let split := splitTapeEquiv (columnRowSampleCount block + block.length)
        (batchedColumnSampleCount rest) Fp tape
      List.ofFn (batchToColumnTape block split.1) ++ List.ofFn (batchedToColumnTape rest split.2) := by
  change List.ofFn (Equiv.cast (congrArg (fun count => Fin count → Fp)
    (columnFullSampleCount_append block rest.flatten).symm) ((splitTapeEquiv (columnFullSampleCount block)
    (columnFullSampleCount rest.flatten) Fp).symm _)) = _
  rw [ofFn_castTape (columnFullSampleCount_append block rest.flatten).symm, ofFn_joinTape]
  rfl

/-- Decode all tails followed by all blinds in each consecutive source batch. -/
def batchedColumnTapeLists {n : ℕ} : List (List (ColumnStep n)) → List Fp → List Fp × List Fp
  | [], _ => ([], [])
  | block :: rest, tape =>
    let rows := columnRowSampleCount block
    let later := batchedColumnTapeLists rest (tape.drop (rows + block.length))
    (tape.take rows ++ later.1, (tape.drop rows).take block.length ++ later.2)

/-- The row-mask counts add across consecutive column schedules. -/
theorem columnRowSampleCount_append {n : ℕ} (first rest : List (ColumnStep n)) :
    columnRowSampleCount (first ++ rest) = columnRowSampleCount first + columnRowSampleCount rest := by
  simp only [columnRowSampleCount_eq_sum, List.map_append, List.sum_append]

/-- The decoder returns at most the declared number of replacement rows. -/
theorem batchedColumnTapeLists_rows_length_le {n : ℕ} (batches : List (List (ColumnStep n)))
    (tape : List Fp) : (batchedColumnTapeLists batches tape).1.length ≤ columnRowSampleCount batches.flatten := by
  induction batches generalizing tape with
  | nil => simp [batchedColumnTapeLists, columnRowSampleCount]
  | cons block rest ih =>
    have hl := ih (tape.drop (columnRowSampleCount block + block.length))
    have ht := List.length_take_le (columnRowSampleCount block) tape
    simp only [batchedColumnTapeLists, List.flatten_cons, List.length_append, columnRowSampleCount_append]
    omega

/-- A short tape can remove returned blinds but never creates extra column slots. -/
theorem batchedColumnTapeLists_blinds_length_le {n : ℕ} (batches : List (List (ColumnStep n)))
    (tape : List Fp) : (batchedColumnTapeLists batches tape).2.length ≤ batches.flatten.length := by
  induction batches generalizing tape with
  | nil => simp [batchedColumnTapeLists]
  | cons block rest ih =>
    have hl := ih (tape.drop (columnRowSampleCount block + block.length))
    have ht := List.length_take_le block.length (tape.drop (columnRowSampleCount block))
    simp only [batchedColumnTapeLists, List.flatten_cons, List.length_append]
    omega

/-- The direct list decoder retains exactly the row and blind subsequences of the existing batch equivalences. -/
theorem batchedColumnTapeLists_result {n : ℕ} (batches : List (List (ColumnStep n)))
    (tape : Fin (batchedColumnSampleCount batches) → Fp) :
    batchedColumnTapeLists batches (List.ofFn tape) =
      (List.ofFn (columnCoinEquiv batches.flatten (batchedToColumnTape batches tape)).1,
        List.ofFn (columnCoinEquiv batches.flatten (batchedToColumnTape batches tape)).2) := by
  induction batches with
  | nil => rfl
  | cons block rest ih =>
    let split := splitTapeEquiv (columnRowSampleCount block + block.length)
      (batchedColumnSampleCount rest) Fp tape
    rw [← columnTapeLists_result, batchedToColumnTape_cons_list]
    change _ = columnTapeLists (block ++ rest.flatten)
      (List.ofFn (batchToColumnTape block split.1) ++ List.ofFn (batchedToColumnTape rest split.2))
    rw [columnTapeLists_append block rest.flatten _ _ (by simp),
      columnTapeLists_result block, batchToColumnTape_fields,
      columnTapeLists_result rest.flatten, ← ih split.2]
    have hrows : List.ofFn (splitTapeEquiv (columnRowSampleCount block) block.length Fp split.1).1 =
        (List.ofFn tape).take (columnRowSampleCount block) := by
      rw [ofFn_splitTape_left, show List.ofFn split.1 = (List.ofFn tape).take
        (columnRowSampleCount block + block.length) from ofFn_splitTape_left _ _ _ _]
      simp only [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    have hblinds : List.ofFn (splitTapeEquiv (columnRowSampleCount block) block.length Fp split.1).2 =
        ((List.ofFn tape).drop (columnRowSampleCount block)).take block.length := by
      rw [ofFn_splitTape_right, show List.ofFn split.1 = (List.ofFn tape).take
        (columnRowSampleCount block + block.length) from ofFn_splitTape_left _ _ _ _]
      exact List.take_drop.symm
    have hlater : List.ofFn split.2 =
        (List.ofFn tape).drop (columnRowSampleCount block + block.length) :=
      ofFn_splitTape_right _ _ _ _
    rw [hrows, hblinds, hlater]
    rfl

end Zcash.Snark.ZeroKnowledge
