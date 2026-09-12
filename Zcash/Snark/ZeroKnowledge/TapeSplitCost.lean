import Zcash.Snark.ZeroKnowledge.ListTraversalCost
import Zcash.Snark.ZeroKnowledge.BatchedTape

namespace Zcash.Snark.ZeroKnowledge

/-- Split a materialized list in one traversal, counting copied prefix cells and reads. -/
def splitListCosted {A : Type*} (read : ℕ) : ℕ → List A → (List A × List A) × ℕ
  | 0, values => (([], values), 1)
  | _ + 1, [] => (([], []), 1)
  | count + 1, first :: rest =>
    let later := splitListCosted read count rest
    ((first :: later.1.1, later.1.2), later.2 + read + 2)

/-- The counted split preserves the original prefix and suffix, including short input. -/
theorem splitListCosted_result {A : Type*} (read count : ℕ) (values : List A) :
    (splitListCosted read count values).1 = (values.take count, values.drop count) := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih => cases values <;> simp only [splitListCosted, ih, List.take_nil, List.drop_nil,
    List.take_succ_cons, List.drop_succ_cons]

/-- A split visits at most the materialized input, for every requested prefix length. -/
theorem splitListCosted_cost_le {A : Type*} (read count : ℕ) (values : List A) :
    (splitListCosted read count values).2 ≤ values.length * (read + 2) + 1 := by
  induction count generalizing values with
  | zero => simp [splitListCosted]
  | succ count ih =>
    cases values with
    | nil => simp [splitListCosted]
    | cons first rest =>
      have h := ih rest
      simp only [splitListCosted, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Both returned blocks remain no longer than the complete input. -/
theorem splitListCosted_lengths_le {A : Type*} (read count : ℕ) (values : List A) :
    (splitListCosted read count values).1.1.length ≤ values.length ∧
      (splitListCosted read count values).1.2.length ≤ values.length := by
  rw [splitListCosted_result]
  simp

/-- Count the actual declared replacement rows, retaining every metadata read and subtraction. -/
def columnRowSampleCountCosted {n : ℕ} : List (ColumnStep n) → ℕ × ℕ
  | [] => (0, 1)
  | step :: rest =>
    let later := columnRowSampleCountCosted rest
    (n - step.firstMasked + later.1, later.2 + 3)

/-- Erasing the counter recovers the existing row-sample budget. -/
theorem columnRowSampleCountCosted_result {n : ℕ} (steps : List (ColumnStep n)) :
    (columnRowSampleCountCosted steps).1 = columnRowSampleCount steps := by
  induction steps <;> simp_all only [columnRowSampleCountCosted, columnRowSampleCount]

/-- Metadata counting is linear in the number of materialized columns. -/
theorem columnRowSampleCountCosted_cost {n : ℕ} (steps : List (ColumnStep n)) :
    (columnRowSampleCountCosted steps).2 = 3 * steps.length + 1 := by
  induction steps with
  | nil => rfl
  | cons step rest ih => simp only [columnRowSampleCountCosted, ih, List.length_cons]; omega

end Zcash.Snark.ZeroKnowledge
