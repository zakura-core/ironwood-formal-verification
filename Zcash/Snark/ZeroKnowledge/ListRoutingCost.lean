import Zcash.Snark.ZeroKnowledge.ListFoldCost

/-!
# Counted routing over materialized lists

These operations charge list traversal, output cells, and bounded-width index
steps. They operate on already materialized input cells. A cell containing a
function does not make future function applications free; its eventual consumer
must retain the supplied access costs.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Read a materialized list with the original default behavior and explicit traversal costs. -/
def getDListCosted {α : Type*} (read : ℕ) (fallback : α) : List α → ℕ → α × ℕ
  | [], _ => (fallback, 1)
  | first :: _, 0 => (first, read + 1)
  | _ :: rest, index + 1 =>
    let value := getDListCosted read fallback rest index
    (value.1, value.2 + 2)

/-- The counted access preserves in-range entries and out-of-range defaults. -/
theorem getDListCosted_result {α : Type*} (read : ℕ) (fallback : α) (values : List α) (index : ℕ) :
    (getDListCosted read fallback values index).1 = values.getD index fallback := by
  induction values generalizing index with
  | nil => simp [getDListCosted]
  | cons first rest ih => cases index <;> simp [getDListCosted, ih]

/-- A failed access traverses at most the input list, even for an arbitrarily large index. -/
theorem getDListCosted_cost_le {α : Type*} (read : ℕ) (fallback : α) (values : List α) (index : ℕ) :
    (getDListCosted read fallback values index).2 ≤ 2 * values.length + read + 1 := by
  induction values generalizing index with
  | nil => simp [getDListCosted]
  | cons first rest ih =>
    cases index with
    | zero => simp [getDListCosted]
    | succ index =>
      have h := ih index
      simp only [getDListCosted, List.length_cons]
      omega

/-- Obtain the actual last cell with a complete traversal counter. -/
def lastListCosted {α : Type*} (read : ℕ) : List α → Option α × ℕ
  | [] => (none, 1)
  | [last] => (some last, read + 2)
  | _ :: second :: rest =>
    let value := lastListCosted read (second :: rest)
    (value.1, value.2 + 2)

/-- The counted last-cell operation has exactly the original optional result. -/
theorem lastListCosted_result {α : Type*} (read : ℕ) (values : List α) :
    (lastListCosted read values).1 = values.getLast? := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons second rest => simp only [lastListCosted, ih, List.getLast?_cons_cons]

/-- The last-cell traversal is linear in the materialized list length. -/
theorem lastListCosted_cost_le {α : Type*} (read : ℕ) (values : List α) :
    (lastListCosted read values).2 ≤ 2 * values.length + read + 1 := by
  induction values with
  | nil => simp [lastListCosted]
  | cons first rest ih =>
    cases rest with
    | nil => simp [lastListCosted]
    | cons second rest =>
      simp only [lastListCosted, List.length_cons] at ih ⊢
      omega

/-- Append materialized lists while charging every copied prefix cell. -/
def appendListCosted {α : Type*} : List α → List α → List α × ℕ
  | [], right => (right, 1)
  | first :: rest, right =>
    let tail := appendListCosted rest right
    (first :: tail.1, tail.2 + 1)

/-- Erasure preserves the original concatenation order. -/
theorem appendListCosted_result {α : Type*} (left right : List α) :
    (appendListCosted left right).1 = left ++ right := by
  induction left <;> simp_all only [appendListCosted, List.nil_append, List.cons_append]

/-- Exact cost of copying the prefix into the concatenated list. -/
theorem appendListCosted_cost {α : Type*} (left right : List α) :
    (appendListCosted left right).2 = left.length + 1 := by
  induction left <;> simp_all only [appendListCosted, List.length_nil, List.length_cons]

/-- Pair materialized lists until the first ends, retaining all list-construction work. -/
def zipListCosted {α β : Type*} : List α → List β → List (α × β) × ℕ
  | first :: left, second :: right =>
    let tail := zipListCosted left right
    ((first, second) :: tail.1, tail.2 + 2)
  | _, _ => ([], 1)

/-- The counted zip has the same truncation and pair order as the original list operation. -/
theorem zipListCosted_result {α β : Type*} (left : List α) (right : List β) :
    (zipListCosted left right).1 = left.zip right := by
  induction left generalizing right with
  | nil => rfl
  | cons first rest ih => cases right <;> simp [zipListCosted, ih]

/-- Pairing is bounded by the left list length on every truncation branch. -/
theorem zipListCosted_cost_le {α β : Type*} (left : List α) (right : List β) :
    (zipListCosted left right).2 ≤ 2 * left.length + 1 := by
  induction left generalizing right with
  | nil => simp [zipListCosted]
  | cons first rest ih =>
    cases right with
    | nil => simp [zipListCosted]
    | cons second right =>
      have h := ih right
      simp only [zipListCosted, List.length_cons]
      omega

/-- Map a materialized list with its actual successive indices and full callback costs. -/
def mapIndexListCosted {α β : Type*} (step : ℕ → α → β × ℕ) : ℕ → List α → List β × ℕ
  | _, [] => ([], 1)
  | start, first :: rest =>
    let value := step start first
    let tail := mapIndexListCosted step (start + 1) rest
    (value.1 :: tail.1, value.2 + tail.2 + 2)

/-- Index generation and mapping reproduce the original zipped range exactly. -/
theorem mapIndexListCosted_result {α β : Type*} (step : ℕ → α → β × ℕ)
    (start : ℕ) (values : List α) :
    (mapIndexListCosted step start values).1 =
      ((List.range' start values.length).zip values).map (fun pair => (step pair.1 pair.2).1) := by
  induction values generalizing start with
  | nil => simp [mapIndexListCosted]
  | cons first rest ih =>
    simp only [mapIndexListCosted, ih, List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons]

/-- Every indexed callback is charged at its actual in-range index. -/
theorem mapIndexListCosted_cost_le {α β : Type*} (step : ℕ → α → β × ℕ)
    (start : ℕ) (values : List α) (budget : ℕ)
    (hstep : ∀ index, start ≤ index → index < start + values.length →
      ∀ value ∈ values, (step index value).2 ≤ budget) :
    (mapIndexListCosted step start values).2 ≤ values.length * (budget + 2) + 1 := by
  induction values generalizing start with
  | nil => simp [mapIndexListCosted]
  | cons first rest ih =>
    have hfirst := hstep start (by omega) (by simp) first (by simp)
    have hrest := ih (start + 1) (fun index hlow hhigh value hvalue =>
      hstep index (by omega) (by simp only [List.length_cons]; omega) value (List.mem_cons_of_mem first hvalue))
    simp only [mapIndexListCosted, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end Zcash.Snark.ZeroKnowledge
