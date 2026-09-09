import Zcash.Snark.ZeroKnowledge.LookupSort
import Zcash.Snark.ZeroKnowledge.ListRoutingCost

/-!
# Counted lookup reservations and row filling

These programs execute the original run plan, membership test, first-occurrence
erasure, reservations, and reverse-fill consumer. Every traversed list cell,
equality test, and constructed result is charged, including failed reservations
and inconsistent fill lengths. The equality price is a supplied primitive cost.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {A : Type*}

/-- Construct the original run-start plan, retaining the equality and traversal costs. -/
def lookupRunPlanCosted [DecidableEq A] (equal : ℕ) (previous : Option A) :
    List A → List (Option A) × ℕ
  | [] => ([], 1)
  | value :: rest =>
    let tail := lookupRunPlanCosted equal (some value) rest
    ((if previous = some value then none else some value) :: tail.1,
      tail.2 + equal + 2)

/-- Erasing the counter gives the original run plan for every input. -/
theorem lookupRunPlanCosted_result [DecidableEq A] (equal : ℕ) (previous : Option A)
    (values : List A) :
    (lookupRunPlanCosted equal previous values).1 = lookupRunPlan previous values := by
  induction values generalizing previous <;> simp_all only [lookupRunPlanCosted, lookupRunPlan]

/-- Exact run-plan cost, including the final empty-list case. -/
theorem lookupRunPlanCosted_cost [DecidableEq A] (equal : ℕ) (previous : Option A)
    (values : List A) :
    (lookupRunPlanCosted equal previous values).2 = values.length * (equal + 2) + 1 := by
  induction values generalizing previous with
  | nil => simp [lookupRunPlanCosted]
  | cons value rest ih =>
    simp only [lookupRunPlanCosted, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Collect reserved values while charging each option inspection and output cell. -/
def lookupReservedCosted : List (Option A) → List A × ℕ
  | [] => ([], 1)
  | value :: rest =>
    let tail := lookupReservedCosted rest
    match value with
    | none => (tail.1, tail.2 + 1)
    | some value => (value :: tail.1, tail.2 + 2)

/-- The reserved values have exactly the original filter-map order. -/
theorem lookupReservedCosted_result (plan : List (Option A)) :
    (lookupReservedCosted plan).1 = plan.filterMap id := by
  induction plan with
  | nil => rfl
  | cons value rest ih => cases value <;> simp [lookupReservedCosted, ih]

/-- Reservation extraction visits at most two structural steps per source slot. -/
theorem lookupReservedCosted_cost_le (plan : List (Option A)) :
    (lookupReservedCosted plan).2 ≤ 2 * plan.length + 1 := by
  induction plan with
  | nil => simp [lookupReservedCosted]
  | cons value rest ih =>
    cases value <;> simp only [lookupReservedCosted, List.length_cons] <;> omega

/-- Search for a value, stopping at the first equality. -/
def lookupContainsCosted [DecidableEq A] (equal : ℕ) (value : A) : List A → Bool × ℕ
  | [] => (false, 1)
  | first :: rest =>
    if value = first then (true, equal + 2) else
      let tail := lookupContainsCosted equal value rest
      (tail.1, tail.2 + equal + 2)

/-- The counted search decides exactly the original membership predicate. -/
theorem lookupContainsCosted_result [DecidableEq A] (equal : ℕ) (value : A) (values : List A) :
    (lookupContainsCosted equal value values).1 = decide (value ∈ values) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    by_cases h : value = first <;> simp [lookupContainsCosted, h, ih]

/-- Both successful and unsuccessful searches fit the complete traversal bound. -/
theorem lookupContainsCosted_cost_le [DecidableEq A] (equal : ℕ) (value : A) (values : List A) :
    (lookupContainsCosted equal value values).2 ≤ values.length * (equal + 2) + 1 := by
  induction values with
  | nil => simp [lookupContainsCosted]
  | cons first rest ih =>
    simp only [lookupContainsCosted, List.length_cons, Nat.add_mul, Nat.one_mul]
    split <;> omega

/-- Erase exactly the first matching occurrence and charge every copied prefix cell. -/
def lookupEraseCosted [DecidableEq A] (equal : ℕ) (value : A) : List A → List A × ℕ
  | [] => ([], 1)
  | first :: rest =>
    if value = first then (rest, equal + 2) else
      let tail := lookupEraseCosted equal value rest
      (first :: tail.1, tail.2 + equal + 2)

/-- Erasing the counter preserves the original first-occurrence erasure. -/
theorem lookupEraseCosted_result [DecidableEq A] (equal : ℕ) (value : A) (values : List A) :
    (lookupEraseCosted equal value values).1 = values.erase value := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    by_cases h : value = first
    · subst first
      simp [lookupEraseCosted]
    · simp [lookupEraseCosted, h, ih, List.erase_cons_tail, Ne.symm h]

/-- The erasure traversal includes the missing-value case. -/
theorem lookupEraseCosted_cost_le [DecidableEq A] (equal : ℕ) (value : A) (values : List A) :
    (lookupEraseCosted equal value values).2 ≤ values.length * (equal + 2) + 1 := by
  induction values with
  | nil => simp [lookupEraseCosted]
  | cons first rest ih =>
    simp only [lookupEraseCosted, List.length_cons, Nat.add_mul, Nat.one_mul]
    split <;> omega

/-- Execute all original reservations, retaining work already done when a value is missing. -/
def reserveLookupValuesCosted [DecidableEq A] (equal : ℕ) :
    List A → List A → Option (List A) × ℕ
  | [], table => (some table, 1)
  | value :: rest, table =>
    let found := lookupContainsCosted equal value table
    if found.1 then
      let erased := lookupEraseCosted equal value table
      let tail := reserveLookupValuesCosted equal rest erased.1
      (tail.1, found.2 + erased.2 + tail.2 + 2)
    else (none, found.2 + 2)

/-- Reservation success, failure, and remaining table agree with the original program. -/
theorem reserveLookupValuesCosted_result [DecidableEq A] (equal : ℕ) (reserved table : List A) :
    (reserveLookupValuesCosted equal reserved table).1 = reserveLookupValues reserved table := by
  induction reserved generalizing table with
  | nil => rfl
  | cons value rest ih =>
    simp only [reserveLookupValuesCosted, lookupContainsCosted_result, decide_eq_true_eq,
      lookupEraseCosted_result, reserveLookupValues]
    split <;> simp_all only

/-- A fixed table-size cap bounds all shrinking intermediate reservation tables. -/
theorem reserveLookupValuesCosted_cost_le_bound [DecidableEq A] (equal : ℕ)
    (reserved table : List A) (size : ℕ) (hsize : table.length ≤ size) :
    (reserveLookupValuesCosted equal reserved table).2 ≤
      reserved.length * (2 * (size * (equal + 2) + 1) + 2) + 1 := by
  induction reserved generalizing table with
  | nil => simp [reserveLookupValuesCosted]
  | cons value rest ih =>
    have hfound : (lookupContainsCosted equal value table).2 ≤ size * (equal + 2) + 1 :=
      (lookupContainsCosted_cost_le equal value table).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right (equal + 2) hsize) 1)
    have herased : (lookupEraseCosted equal value table).2 ≤ size * (equal + 2) + 1 :=
      (lookupEraseCosted_cost_le equal value table).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right (equal + 2) hsize) 1)
    have htail := ih (lookupEraseCosted equal value table).1 (by
      rw [lookupEraseCosted_result]
      exact (List.length_erase_le).trans hsize)
    simp only [reserveLookupValuesCosted, List.length_cons, Nat.add_mul, Nat.one_mul]
    split <;> omega

/-- Explicit polynomial reservation bound in the two input lengths and equality price. -/
theorem reserveLookupValuesCosted_cost_le [DecidableEq A] (equal : ℕ) (reserved table : List A) :
    (reserveLookupValuesCosted equal reserved table).2 ≤
      reserved.length * (2 * (table.length * (equal + 2) + 1) + 2) + 1 :=
  reserveLookupValuesCosted_cost_le_bound equal reserved table table.length le_rfl

/-- Fill the complete plan, retaining all earlier work when the unused values do not fit. -/
def fillLookupPlanCosted : List (Option A) → List A → Option (List A) × ℕ
  | [], [] => (some [], 1)
  | [], _ :: _ => (none, 1)
  | some value :: rest, unused =>
    let tail := fillLookupPlanCosted rest unused
    (tail.1.map (List.cons value), tail.2 + 3)
  | none :: rest, value :: unused =>
    let tail := fillLookupPlanCosted rest unused
    (tail.1.map (List.cons value), tail.2 + 3)
  | none :: _, [] => (none, 1)

/-- The counted fill preserves every original failure and output row. -/
theorem fillLookupPlanCosted_result (plan : List (Option A)) (unused : List A) :
    (fillLookupPlanCosted plan unused).1 = fillLookupPlan plan unused := by
  induction plan generalizing unused with
  | nil => cases unused <;> rfl
  | cons entry rest ih =>
    cases entry with
    | some value => simp only [fillLookupPlanCosted, ih, fillLookupPlan]
    | none => cases unused <;> simp only [fillLookupPlanCosted, ih, fillLookupPlan]

/-- Every fill branch is bounded by the original plan length, including early failure. -/
theorem fillLookupPlanCosted_cost_le (plan : List (Option A)) (unused : List A) :
    (fillLookupPlanCosted plan unused).2 ≤ 3 * plan.length + 1 := by
  induction plan generalizing unused with
  | nil => cases unused <;> simp [fillLookupPlanCosted]
  | cons entry rest ih =>
    cases entry with
    | some value =>
      have h := ih unused
      simp only [fillLookupPlanCosted, List.length_cons]
      omega
    | none =>
      cases unused with
      | nil => simp [fillLookupPlanCosted]
      | cons value unused =>
        have h := ih unused
        simp only [fillLookupPlanCosted, List.length_cons]
        omega

end Zcash.Snark.ZeroKnowledge
