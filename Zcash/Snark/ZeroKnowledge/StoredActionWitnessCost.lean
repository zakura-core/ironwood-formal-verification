import Zcash.Snark.ZeroKnowledge.StoredRowsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Materialize the supplied actual Action advice witness in Action/column/row order. -/
def encodeActionWitness {actions : ℕ} (witness : Fin actions → Fin 10 → Fin 2048 → Fp) : List (List (List Fp)) :=
  List.ofFn fun action => List.ofFn fun column => List.ofFn (witness action column)

/-- Read a stored advice cell, counting the Action, column, and row traversals. -/
def storedActionWitnessRowCosted (read : ℕ) (witness : List (List (List Fp)))
    (action : ℕ) (column : Fin 10) (row : Fin 2048) : Fp × ℕ :=
  let columns := getDListCosted read [] witness action
  let value := storedMatrixEntryCosted read (0 : Fp) columns.1 column.val row.val
  (value.1, columns.2 + value.2 + 1)

/-- The stored advice reader recovers every original supplied witness cell. -/
theorem storedActionWitnessRowCosted_result (read : ℕ) {actions : ℕ}
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (action : Fin actions) (column : Fin 10) (row : Fin 2048) :
    (storedActionWitnessRowCosted read (encodeActionWitness witness) action.val column row).1 = witness action column row := by
  unfold storedActionWitnessRowCosted
  change (storedMatrixEntryCosted read (0 : Fp)
    (getDListCosted read [] (encodeActionWitness witness) action.val).1 column.val row.val).1 = _
  rewrite [show (getDListCosted read [] (encodeActionWitness witness) action.val).1 =
      List.ofFn (fun column => List.ofFn (witness action column)) from getDListCosted_ofFn_result read [] _ action]
  exact storedMatrixEntryCosted_ofFn read (0 : Fp) (witness action) column row

/-- The complete advice-cell access price follows from the actual three-dimensional input storage. -/
theorem storedActionWitnessRowCosted_cost_le (read : ℕ) {actions : ℕ}
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (action : Fin actions) (column : Fin 10) (row : Fin 2048) :
    (storedActionWitnessRowCosted read (encodeActionWitness witness) action.val column row).2 ≤
      2 * actions + 3 * read + 4121 := by
  have hcolumns := getDListCosted_cost_le read [] (encodeActionWitness witness) action.val
  have he : (getDListCosted read [] (encodeActionWitness witness) action.val).1 =
      List.ofFn (fun column => List.ofFn (witness action column)) := getDListCosted_ofFn_result read [] _ action
  have hv := storedMatrixEntryCosted_cost_le read (0 : Fp)
    (List.ofFn (fun column => List.ofFn (witness action column))) column.val row.val 2048 (by
      intro values hvalues
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hvalues
      simp only [List.length_ofFn, le_refl])
  simp only [encodeActionWitness, List.length_ofFn] at hcolumns hv
  change (getDListCosted read [] (encodeActionWitness witness) action.val).2 ≤ 2 * actions + read + 1 at hcolumns
  unfold storedActionWitnessRowCosted
  change (getDListCosted read [] (encodeActionWitness witness) action.val).2 +
    (storedMatrixEntryCosted read (0 : Fp) (getDListCosted read [] (encodeActionWitness witness) action.val).1
      column.val row.val).2 + 1 ≤ _
  rewrite [he]
  omega

end Zcash.Snark.ZeroKnowledge
