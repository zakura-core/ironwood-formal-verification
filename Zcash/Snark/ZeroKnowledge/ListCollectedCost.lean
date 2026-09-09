import Zcash.Snark.ZeroKnowledge.ListRoutingCost

/-!
# Counted list collection with per-entry costs

Collection retains the complete supplied callback costs and pays for every
copied output cell. Finite-index collection also charges successor adapters.
The result theorems preserve the original map, flat-map, and flatten order.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Per-entry callback budgets bound the existing counted map without a uniform-cost assumption. -/
theorem mapListCosted_cost_le_sum {α β : Type*} (step : α → β × ℕ) (values : List α)
    (budget : α → ℕ) (hstep : ∀ value ∈ values, (step value).2 ≤ budget value) :
    (mapListCosted step values).2 ≤ (values.map budget).sum + values.length + 1 := by
  induction values with
  | nil => simp [mapListCosted]
  | cons first rest ih =>
    have hfirst := hstep first (by simp)
    have hrest := ih (fun value hvalue => hstep value (List.mem_cons_of_mem first hvalue))
    simp only [mapListCosted, List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Collect computed lists and charge each produced and concatenated cell. -/
def flatMapListCosted {α β : Type*} (step : α → List β × ℕ) : List α → List β × ℕ
  | [] => ([], 1)
  | first :: rest =>
    let value := step first
    let tail := flatMapListCosted step rest
    let joined := appendListCosted value.1 tail.1
    (joined.1, value.2 + tail.2 + joined.2 + 1)

/-- Count erasure is exactly the original ordered flat-map. -/
theorem flatMapListCosted_result {α β : Type*} (step : α → List β × ℕ) (values : List α) :
    (flatMapListCosted step values).1 = values.flatMap (fun value => (step value).1) := by
  induction values <;>
    simp_all only [flatMapListCosted, appendListCosted_result, List.flatMap_nil, List.flatMap_cons]

/-- The full collection bound retains each callback and its actual output size. -/
theorem flatMapListCosted_cost_le_sum {α β : Type*} (step : α → List β × ℕ) (values : List α)
    (budget length : α → ℕ)
    (hstep : ∀ value ∈ values, (step value).2 ≤ budget value)
    (hlength : ∀ value ∈ values, (step value).1.length ≤ length value) :
    (flatMapListCosted step values).2 ≤
      (values.map (fun value => budget value + length value + 2)).sum + 1 := by
  induction values with
  | nil => simp [flatMapListCosted]
  | cons first rest ih =>
    have hfirst := hstep first (by simp)
    have hsize := hlength first (by simp)
    have hrest := ih (fun value hvalue => hstep value (List.mem_cons_of_mem first hvalue))
      (fun value hvalue => hlength value (List.mem_cons_of_mem first hvalue))
    simp only [flatMapListCosted, appendListCosted_cost, List.map_cons, List.sum_cons]
    omega

/-- Collect a finite vector of computed lists, including every successor-index adapter. -/
def flattenFinCosted {α : Type*} : {count : ℕ} → (Fin count → List α × ℕ) → List α × ℕ
  | 0, _ => ([], 1)
  | count + 1, read =>
    let first := read 0
    let rest := flattenFinCosted (count := count) fun index =>
      let value := read index.succ
      (value.1, value.2 + 1)
    let joined := appendListCosted first.1 rest.1
    (joined.1, first.2 + rest.2 + joined.2 + 1)

/-- The materialized finite collection has exactly the original flatten order. -/
theorem flattenFinCosted_result {α : Type*} {count : ℕ} (read : Fin count → List α × ℕ) :
    (flattenFinCosted read).1 = (List.ofFn (fun index => (read index).1)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [flattenFinCosted, appendListCosted_result, ih, List.ofFn_succ, List.flatten_cons]

/-- Complete finite-collection cost with uniform callback and output-length bounds. -/
theorem flattenFinCosted_cost_le {α : Type*} {count : ℕ} (read : Fin count → List α × ℕ)
    (budget length : ℕ) (hread : ∀ index, (read index).2 ≤ budget)
    (hlength : ∀ index, (read index).1.length ≤ length) :
    (flattenFinCosted read).2 ≤ count * (budget + length + 2) + count * count + 1 := by
  induction count generalizing budget with
  | zero => simp [flattenFinCosted]
  | succ count ih =>
    have hfirst := hread 0
    have hsize := hlength 0
    have hrest := ih (fun index => ((read index.succ).1, (read index.succ).2 + 1))
      (budget + 1) (fun index => Nat.add_le_add_right (hread index.succ) 1)
      (fun index => hlength index.succ)
    simp only [flattenFinCosted, appendListCosted_cost]
    nlinarith

end Zcash.Snark.ZeroKnowledge
