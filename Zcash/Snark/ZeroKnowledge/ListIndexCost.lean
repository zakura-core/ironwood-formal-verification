import Zcash.Snark.ZeroKnowledge.ListRoutingCost

namespace Zcash.Snark.ZeroKnowledge

/-- Count the actual equality tests and traversal of a list's first matching index. -/
def idxOfListCosted {α : Type*} [BEq α] (equal : ℕ) (value : α) : List α → ℕ × ℕ
  | [] => (0, 1)
  | first :: rest =>
    if first == value then (0, equal + 1) else
      let result := idxOfListCosted equal value rest
      (result.1 + 1, result.2 + equal + 2)

/-- Erasure preserves the original equality predicate and the not-found length default. -/
theorem idxOfListCosted_result {α : Type*} [BEq α] (equal : ℕ) (value : α) (values : List α) :
    (idxOfListCosted equal value values).1 = values.idxOf value := by
  induction values with
  | nil => simp [idxOfListCosted]
  | cons first rest ih =>
    cases h : first == value <;> simp [idxOfListCosted, List.idxOf_cons, h, ih]

/-- All equality tests, index increments, and list traversal fit the explicit linear bound. -/
theorem idxOfListCosted_cost_le {α : Type*} [BEq α] (equal : ℕ) (value : α) (values : List α) :
    (idxOfListCosted equal value values).2 ≤ values.length * (equal + 2) + 1 := by
  induction values with
  | nil => simp [idxOfListCosted]
  | cons first rest ih =>
    cases h : first == value <;> simp only [idxOfListCosted, h, Bool.false_eq_true, ↓reduceIte,
      List.length_cons]
    all_goals nlinarith

end Zcash.Snark.ZeroKnowledge
