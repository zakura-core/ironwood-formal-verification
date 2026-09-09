import Zcash.Snark.ZeroKnowledge.PrivateColumnOrderCost
import Zcash.Snark.ZeroKnowledge.ListIndexCost
import Zcash.Snark.ZeroKnowledge.PlonkOpening

/-!
# Counted routing of disclosed private-column values

The algorithm constructs and searches the original column order, traverses the
materialized column list, and invokes the selected reader with its full cost.
Absent columns retain the original zero-function default.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- A counted list read preserves a property shared by the fallback and every stored entry. -/
theorem getDListCosted_property {α : Type*} (read : ℕ) (fallback : α) (values : List α)
    (property : α → Prop) (hfallback : property fallback)
    (hvalues : ∀ value ∈ values, property value) (index : ℕ) :
    property (getDListCosted read fallback values index).1 := by
  induction values generalizing index with
  | nil => exact hfallback
  | cons first rest ih =>
    cases index with
    | zero => exact hvalues first (by simp)
    | succ index =>
      exact ih (fun value hvalue => hvalues value (List.mem_cons_of_mem first hvalue)) index

/-- Locate a column by constructing and searching the exact original schedule. -/
def privateColumnIndexCosted {actions : ℕ} (equal : ℕ) (id : PrivateColumnId actions) : ℕ × ℕ :=
  let order := privateColumnOrderCosted actions
  let result := idxOfListCosted equal id order.1
  (result.1, order.2 + result.2 + 1)

/-- The counted index is the original private-column index, without assuming constant-time lookup. -/
theorem privateColumnIndexCosted_result {actions : ℕ} (equal : ℕ) (id : PrivateColumnId actions) :
    (privateColumnIndexCosted equal id).1 = (privateColumnIndex id).val := by
  simp only [privateColumnIndexCosted, idxOfListCosted_result, privateColumnOrderCosted_result,
    privateColumnIndex]

/-- Every routed index is within the exact original commitment range. -/
theorem privateColumnIndexCosted_lt {actions : ℕ} (equal : ℕ) (id : PrivateColumnId actions) :
    (privateColumnIndexCosted equal id).1 < 22 * actions := by
  rw [privateColumnIndexCosted_result]
  exact (privateColumnIndex id).isLt

/-- The index budget counts both schedule construction and every compared identifier. -/
theorem privateColumnIndexCosted_cost_le {actions : ℕ} (equal : ℕ) (id : PrivateColumnId actions) :
    (privateColumnIndexCosted equal id).2 ≤
      4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) + 12 := by
  have horder := privateColumnOrderCosted_cost_le actions
  have hindex := idxOfListCosted_cost_le equal id (privateColumnOrderCosted actions).1
  rw [privateColumnOrderCosted_length] at hindex
  dsimp only [privateColumnIndexCosted]
  omega

/-- Route and evaluate one disclosed scalar, retaining the full cost of the selected function. -/
def privateColumnViewCosted {actions count : ℕ} (equal read : ℕ)
    (views : List (Fin count → Fp × ℕ)) (id : PrivateColumnId actions) (point : Fin count) : Fp × ℕ :=
  let index := privateColumnIndexCosted equal id
  let column := getDListCosted read (fun _ => (0, 1)) views index.1
  let value := column.1 point
  (value.1, index.2 + column.2 + value.2 + 1)

/-- Erasure is the original disclosed-column lookup, including its zero fallback. -/
theorem privateColumnViewCosted_result {actions count : ℕ} (equal read : ℕ)
    (views : List (Fin count → Fp × ℕ)) (id : PrivateColumnId actions) (point : Fin count) :
    (privateColumnViewCosted equal read views id point).1 =
      privateColumnView (views.map (fun column index => (column index).1)) id point := by
  simp only [privateColumnViewCosted, getDListCosted_result, privateColumnIndexCosted_result,
    privateColumnView, privateColumnIndex]
  have h := List.getD_map (l := views) (n := (privateColumnOrder actions).idxOf id)
    (d := fun _ : Fin count => ((0 : Fp), 1)) (fun column index => (column index).1)
  exact (congrFun h point).symm

/-- All routing and reader work is bounded, including malformed views with missing columns. -/
theorem privateColumnViewCosted_cost_le {actions count : ℕ} (equal read : ℕ)
    (views : List (Fin count → Fp × ℕ)) (id : PrivateColumnId actions) (point : Fin count)
    (access : ℕ) (hread : ∀ column ∈ views, ∀ index, (column index).2 ≤ access) :
    (privateColumnViewCosted equal read views id point).2 ≤
      4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
        2 * views.length + read + access + 15 := by
  have hindex := privateColumnIndexCosted_cost_le equal id
  have hcolumn := getDListCosted_cost_le read (fun _ : Fin count => ((0 : Fp), 1))
    views (privateColumnIndexCosted equal id).1
  have hvalue := getDListCosted_property read (fun _ : Fin count => ((0 : Fp), 1)) views
    (fun column => (column point).2 ≤ access + 1) (by simp)
    (fun column hmem => (hread column hmem point).trans (Nat.le_succ access))
    (privateColumnIndexCosted equal id).1
  dsimp only [privateColumnViewCosted]
  omega

end Zcash.Snark.ZeroKnowledge
