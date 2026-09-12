import Zcash.Snark.ZeroKnowledge.IpaProver

/-!
# Counted finite materialization and arithmetic

The finite-vector operations retain the complete supplied reader cost, including
all successor-index adapters. List mapping retains the full callback cost.
Materialization constructs every returned list cell, and summation charges every
addition. Bounded-exponent powering executes an explicit multiplication loop.
Each erasure theorem identifies the existing mathematical operation exactly.

The costs are structural units for bounded-width indexing and caller-priced
arithmetic primitives. A function stored in a list remains a function: this
module does not claim to have evaluated its future applications. Callers must
carry those access costs into the eventual consumer.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Materialize a finite vector, charging its supplied readers and index adapters. -/
def ofFnCosted {α : Type*} : {count : ℕ} → (Fin count → α × ℕ) → List α × ℕ
  | 0, _ => ([], 1)
  | count + 1, read =>
    let first := read 0
    let rest := ofFnCosted (count := count) fun index =>
      let value := read index.succ
      (value.1, value.2 + 1)
    (first.1 :: rest.1, first.2 + rest.2 + 1)

/-- Every returned list element is the corresponding original reader result. -/
theorem ofFnCosted_result {α : Type*} {count : ℕ} (read : Fin count → α × ℕ) :
    (ofFnCosted read).1 = List.ofFn (fun index => (read index).1) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [ofFnCosted, ih, List.ofFn_succ]

/-- The output is fully materialized and has exactly the requested length. -/
theorem ofFnCosted_length {α : Type*} {count : ℕ} (read : Fin count → α × ℕ) :
    (ofFnCosted read).1.length = count := by rw [ofFnCosted_result, List.length_ofFn]

/-- The materialization bound includes all reads and list construction. -/
theorem ofFnCosted_cost_le {α : Type*} {count : ℕ} (read : Fin count → α × ℕ)
    (access : ℕ) (haccess : ∀ index, (read index).2 ≤ access) :
    (ofFnCosted read).2 ≤ count * (access + 1) + count * count + 1 := by
  induction count generalizing access with
  | zero => simp [ofFnCosted]
  | succ count ih =>
    have rest := ih (fun index => ((read index.succ).1, (read index.succ).2 + 1))
      (access + 1) (fun index => Nat.add_le_add_right (haccess index.succ) 1)
    have first := haccess 0
    simp only [ofFnCosted]
    nlinarith

/-- Map materialized lists without discarding any supplied callback's work. -/
def mapListCosted {α β : Type*} (step : α → β × ℕ) : List α → List β × ℕ
  | [] => ([], 1)
  | first :: rest =>
    let value := step first
    let tail := mapListCosted step rest
    (value.1 :: tail.1, value.2 + tail.2 + 1)

/-- Erasure of the counted map is the ordinary list map. -/
theorem mapListCosted_result {α β : Type*} (step : α → β × ℕ) (values : List α) :
    (mapListCosted step values).1 = values.map (fun value => (step value).1) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [mapListCosted, ih, List.map_cons]

/-- A complete per-element callback bound gives a bound on the materialized map. -/
theorem mapListCosted_cost_le {α β : Type*} (step : α → β × ℕ) (values : List α)
    (bound : ℕ) (hstep : ∀ value ∈ values, (step value).2 ≤ bound) :
    (mapListCosted step values).2 ≤ values.length * (bound + 1) + 1 := by
  induction values with
  | nil => simp [mapListCosted]
  | cons first rest ih =>
    have hfirst := hstep first (by simp)
    have hrest := ih (fun value hvalue => hstep value (List.mem_cons_of_mem first hvalue))
    simp only [mapListCosted, List.length_cons]
    nlinarith

/-- A counted finite sum includes reader adapters, case tests, and every addition. -/
def sumFinCosted {α : Type*} [AddCommMonoid α] (add : ℕ) :
    {count : ℕ} → (Fin count → α × ℕ) → α × ℕ
  | 0, _ => (0, 1)
  | count + 1, read =>
    let first := read 0
    let rest := sumFinCosted add (count := count) fun index =>
      let value := read index.succ
      (value.1, value.2 + 1)
    (first.1 + rest.1, first.2 + rest.2 + add + 1)

/-- Cost erasure gives the exact existing finite sum. -/
theorem sumFinCosted_result {α : Type*} [AddCommMonoid α] (add : ℕ) {count : ℕ}
    (read : Fin count → α × ℕ) :
    (sumFinCosted add read).1 = ∑ index, (read index).1 := by
  induction count with
  | zero => simp [sumFinCosted]
  | succ count ih => simp only [sumFinCosted, ih, Fin.sum_univ_succ]

/-- The finite-sum bound retains the complete supplied reader cost. -/
theorem sumFinCosted_cost_le {α : Type*} [AddCommMonoid α] (add : ℕ) {count : ℕ}
    (read : Fin count → α × ℕ) (access : ℕ) (haccess : ∀ index, (read index).2 ≤ access) :
    (sumFinCosted add read).2 ≤ count * (access + add + 1) + count * count + 1 := by
  induction count generalizing access with
  | zero => simp [sumFinCosted]
  | succ count ih =>
    have rest := ih (fun index => ((read index.succ).1, (read index.succ).2 + 1))
      (access + 1) (fun index => Nat.add_le_add_right (haccess index.succ) 1)
    have first := haccess 0
    simp only [sumFinCosted]
    nlinarith

/-- Compute a bounded-exponent field power with an explicit multiplication counter. -/
def fieldPowerCosted {F : Type*} [Monoid F] (multiply : ℕ) (base : F) : ℕ → F × ℕ
  | 0 => (1, 1)
  | exponent + 1 =>
    let previous := fieldPowerCosted multiply base exponent
    (previous.1 * base, previous.2 + multiply + 1)

/-- The counted power has exactly the existing exponentiation result. -/
theorem fieldPowerCosted_result {F : Type*} [Monoid F] (multiply : ℕ) (base : F) (exponent : ℕ) :
    (fieldPowerCosted multiply base exponent).1 = base ^ exponent := by
  induction exponent with
  | zero => simp [fieldPowerCosted]
  | succ exponent ih => simp only [fieldPowerCosted, ih, pow_succ]

/-- Exact cost of the bounded-exponent powering loop. -/
theorem fieldPowerCosted_cost {F : Type*} [Monoid F] (multiply : ℕ) (base : F) (exponent : ℕ) :
    (fieldPowerCosted multiply base exponent).2 = exponent * (multiply + 1) + 1 := by
  induction exponent with
  | zero => simp [fieldPowerCosted]
  | succ exponent ih => simp only [fieldPowerCosted, ih, Nat.add_mul, Nat.one_mul]; omega

end Zcash.Snark.ZeroKnowledge
