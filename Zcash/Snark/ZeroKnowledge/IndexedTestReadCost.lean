import Zcash.Snark.ZeroKnowledge.ListRoutingCost

namespace Zcash.Snark.ZeroKnowledge

/-- A direct-index test read stops after its supplied address, even on arbitrarily long inputs. -/
theorem getDListCosted_cost_le_index {α : Type*} (read : ℕ) (fallback : α)
    (values : List α) (index : ℕ) :
    (getDListCosted read fallback values index).2 ≤ 2 * index + read + 1 := by
  induction values generalizing index with
  | nil => simp only [getDListCosted]; omega
  | cons value later ih =>
    cases index with
    | zero => simp only [getDListCosted, Nat.mul_zero, Nat.zero_add, le_refl]
    | succ index =>
      have h := ih index
      simp only [getDListCosted]
      omega

/-- A counted optional read distinguishes a missing entry from any present default-valued entry. -/
def getOptionListCosted {α : Type*} (read : ℕ) : List α → ℕ → Option α × ℕ
  | [], _ => (none, 1)
  | first :: _, 0 => (some first, read + 2)
  | _ :: rest, index + 1 =>
    let value := getOptionListCosted read rest index
    (value.1, value.2 + 2)

theorem getOptionListCosted_result {α : Type*} (read : ℕ) (values : List α) (index : ℕ) :
    (getOptionListCosted read values index).1 = values[index]? := by
  induction values generalizing index with
  | nil => rfl
  | cons value later ih => cases index <;> simp only [getOptionListCosted, ih, List.getElem?_cons_zero, List.getElem?_cons_succ]

theorem getOptionListCosted_cost_le {α : Type*} (read : ℕ) (values : List α) (index : ℕ) :
    (getOptionListCosted read values index).2 ≤ 2 * index + read + 2 := by
  induction values generalizing index with
  | nil => simp only [getOptionListCosted]; omega
  | cons value later ih =>
    cases index with
    | zero => simp only [getOptionListCosted, Nat.mul_zero, Nat.zero_add, le_refl]
    | succ index =>
      have h := ih index
      simp only [getOptionListCosted]
      omega

end Zcash.Snark.ZeroKnowledge
