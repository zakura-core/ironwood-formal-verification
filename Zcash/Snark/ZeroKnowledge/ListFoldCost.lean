import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

namespace Zcash.Snark.ZeroKnowledge

/-- Fold a materialized list, retaining every callback cost and recursive case. -/
def foldlCosted {α β : Type*} (step : β → α → β × ℕ) : List α → β × ℕ → β × ℕ
  | [], initial => (initial.1, initial.2 + 1)
  | first :: rest, initial =>
    let next := step initial.1 first
    foldlCosted step rest (next.1, initial.2 + next.2 + 1)

/-- Cost erasure gives the same fold over the callback's actual returned values. -/
theorem foldlCosted_result {α β : Type*} (step : β → α → β × ℕ)
    (values : List α) (initial : β × ℕ) :
    (foldlCosted step values initial).1 =
      values.foldl (fun state value => (step state value).1) initial.1 := by
  induction values generalizing initial with
  | nil => rfl
  | cons first rest ih => simp only [foldlCosted, ih, List.foldl_cons]

/-- A state invariant is preserved through the complete counted fold. -/
theorem foldlCosted_invariant {α β : Type*} (step : β → α → β × ℕ)
    (values : List α) (initial : β × ℕ) (invariant : β → Prop)
    (hinit : invariant initial.1)
    (hstep : ∀ state, invariant state → ∀ value ∈ values, invariant (step state value).1) :
    invariant (foldlCosted step values initial).1 := by
  induction values generalizing initial with
  | nil => exact hinit
  | cons first rest ih =>
    exact ih ((step initial.1 first).1, initial.2 + (step initial.1 first).2 + 1)
      (hstep initial.1 hinit first (by simp))
      (fun state hstate value hvalue => hstep state hstate value (List.mem_cons_of_mem first hvalue))

/-- Per-element callback bounds compose without treating arbitrary host computations as free. -/
theorem foldlCosted_cost_le_sum {α β : Type*} (step : β → α → β × ℕ)
    (values : List α) (initial : β × ℕ) (invariant : β → Prop) (budget : α → ℕ)
    (hinit : invariant initial.1)
    (hstep : ∀ state, invariant state → ∀ value ∈ values, invariant (step state value).1)
    (hcost : ∀ state, invariant state → ∀ value ∈ values, (step state value).2 ≤ budget value) :
    (foldlCosted step values initial).2 ≤ initial.2 + (values.map budget).sum + values.length + 1 := by
  induction values generalizing initial with
  | nil => simp [foldlCosted]
  | cons first rest ih =>
    have hfirst := hcost initial.1 hinit first (by simp)
    have hrest := ih ((step initial.1 first).1, initial.2 + (step initial.1 first).2 + 1)
      (hstep initial.1 hinit first (by simp))
      (fun state hstate value hvalue => hstep state hstate value (List.mem_cons_of_mem first hvalue))
      (fun state hstate value hvalue => hcost state hstate value (List.mem_cons_of_mem first hvalue))
    simp only [foldlCosted, List.map_cons, List.sum_cons, List.length_cons]
    omega

end Zcash.Snark.ZeroKnowledge
