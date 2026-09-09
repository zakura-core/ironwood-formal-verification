import Zcash.Snark.ZeroKnowledge.LookupPlanCost

namespace Zcash.Snark.ZeroKnowledge

/-- Remove repeated values with counted membership scans and list construction. -/
def distinctListCosted {A : Type*} [DecidableEq A] (equal : ℕ) : List A → List A × ℕ
  | [] => ([], 1)
  | first :: rest =>
    let tail := distinctListCosted equal rest
    let found := lookupContainsCosted equal first tail.1
    (if found.1 then tail.1 else first :: tail.1, tail.2 + found.2 + 3)

/-- Deduplication preserves precisely the original set of values. -/
theorem distinctListCosted_mem {A : Type*} [DecidableEq A] (equal : ℕ) (values : List A) (value : A) :
    value ∈ (distinctListCosted equal values).1 ↔ value ∈ values := by
  induction values generalizing value with
  | nil => simp [distinctListCosted]
  | cons first rest ih =>
    simp only [distinctListCosted, lookupContainsCosted_result, decide_eq_true_eq]
    split <;> simp_all

/-- The counted output contains no repeated entry. -/
theorem distinctListCosted_nodup {A : Type*} [DecidableEq A] (equal : ℕ) (values : List A) :
    (distinctListCosted equal values).1.Nodup := by
  induction values with
  | nil => simp [distinctListCosted]
  | cons first rest ih =>
    simp only [distinctListCosted, lookupContainsCosted_result, decide_eq_true_eq]
    split <;> simp_all

/-- The retained list never exceeds the original materialized width. -/
theorem distinctListCosted_length_le {A : Type*} [DecidableEq A] (equal : ℕ) (values : List A) :
    (distinctListCosted equal values).1.length ≤ values.length := by
  induction values with
  | nil => simp [distinctListCosted]
  | cons first rest ih =>
    simp only [distinctListCosted, List.length_cons]
    split
    · exact ih.trans (Nat.le_succ rest.length)
    · exact Nat.add_le_add_right ih 1

/-- Equality scans and all output work fit a quadratic input-size budget. -/
theorem distinctListCosted_cost_le {A : Type*} [DecidableEq A] (equal : ℕ) (values : List A) :
    (distinctListCosted equal values).2 ≤ values.length * values.length * (equal + 2) + 4 * values.length + 1 := by
  induction values with
  | nil => simp [distinctListCosted]
  | cons first rest ih =>
    have hn := distinctListCosted_length_le equal rest
    have hf := lookupContainsCosted_cost_le equal first (distinctListCosted equal rest).1
    have hs : (lookupContainsCosted equal first (distinctListCosted equal rest).1).2 ≤
        rest.length * (equal + 2) + 1 := hf.trans (by gcongr)
    dsimp only [distinctListCosted]
    simp only [List.length_cons]
    nlinarith

/-- The returned values have exactly the source finite set, independently of duplicate positions. -/
theorem distinctListCosted_toFinset {A : Type*} [DecidableEq A] (equal : ℕ) (values : List A) :
    (distinctListCosted equal values).1.toFinset = values.toFinset := by
  ext value
  simp only [List.mem_toFinset, distinctListCosted_mem]

end Zcash.Snark.ZeroKnowledge
