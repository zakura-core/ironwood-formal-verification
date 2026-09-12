import Zcash.Snark.ZeroKnowledge.ListRoutingCost

namespace Zcash.Snark.ZeroKnowledge

/-- A bounded-index list read with explicit traversal and element-access costs, needing no fallback value. -/
def getFinListCosted {α : Type*} (read : ℕ) : (values : List α) → Fin values.length → α × ℕ
  | [], index => Fin.elim0 index
  | first :: _, ⟨0, _⟩ => (first, read + 1)
  | _ :: rest, ⟨index + 1, h⟩ =>
    -- Match the index directly: recursion through `Fin.cases` duplicates work in the interpreter.
    let value := getFinListCosted read rest ⟨index, Nat.lt_of_succ_lt_succ h⟩
    (value.1, value.2 + 2)

/-- Cost erasure is the original proof-bounded list access. -/
theorem getFinListCosted_result {α : Type*} (read : ℕ) (values : List α) (index : Fin values.length) :
    (getFinListCosted read values index).1 = values[index.val] := by
  induction values with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · rfl
    · simpa only [getFinListCosted, Fin.val_succ, List.getElem_cons_succ] using ih index

/-- Every bounded list read has the same linear traversal bound as the totalized reader. -/
theorem getFinListCosted_cost_le {α : Type*} (read : ℕ) (values : List α) (index : Fin values.length) :
    (getFinListCosted read values index).2 ≤ 2 * values.length + read + 1 := by
  induction values with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · change read + 1 ≤ 2 * (rest.length + 1) + read + 1
      omega
    · change (getFinListCosted read rest index).2 + 2 ≤ 2 * (rest.length + 1) + read + 1
      have h := ih index
      omega

end Zcash.Snark.ZeroKnowledge
