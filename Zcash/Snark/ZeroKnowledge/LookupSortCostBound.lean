import Zcash.Snark.ZeroKnowledge.LookupSortCost

namespace Zcash.Snark.ZeroKnowledge

variable {A : Type*}

/-- A successful reservation can only remove entries from its original table. -/
theorem reserveLookupValuesCosted_remaining_length [DecidableEq A] (equal : ℕ)
    (reserved table remaining : List A)
    (h : (reserveLookupValuesCosted equal reserved table).1 = some remaining) :
    remaining.length ≤ table.length := by
  rw [reserveLookupValuesCosted_result] at h
  have hlength := (reserveLookupValues_perm reserved table remaining h).length_eq
  simp only [List.length_append] at hlength
  omega

/-- Complete polynomial sorter budget, including both sorted inputs and every failure path. -/
def lookupSortColumnsCostBudget (compare equal keyCost inputSize tableSize : ℕ) : ℕ :=
  (inputSize ^ 2 + tableSize ^ 2) * (2 * keyCost + compare + 6) +
    inputSize * (2 * (tableSize * (equal + 2) + 1) + equal + 16) + 4 * tableSize + 32

/-- All original lookup-sort branches fit the same explicit input-size budget. -/
theorem lookupSortColumnsCosted_cost_le [DecidableEq A] (key : A → ℕ × ℕ) (compare equal : ℕ)
    (input table : List A) (keyCost : ℕ) (hkey : ∀ value, (key value).2 ≤ keyCost) :
    (lookupSortColumnsCosted key compare equal input table).2 ≤
      lookupSortColumnsCostBudget compare equal keyCost input.length table.length := by
  let b := canonicalLookupSortCosted key compare input
  let sortedTable := canonicalLookupSortCosted key compare table
  let plan := lookupRunPlanCosted equal (none : Option A) b.1
  let reserved := lookupReservedCosted plan.1
  let unused := reserveLookupValuesCosted equal reserved.1 sortedTable.1
  have hbSize : b.1.length = input.length := canonicalLookupSortCosted_length key compare input
  have htSize : sortedTable.1.length = table.length := canonicalLookupSortCosted_length key compare table
  have hpSize : plan.1.length = input.length := by
    rw [lookupRunPlanCosted_result, lookupRunPlan_length, hbSize]
  have hrSize : reserved.1.length ≤ input.length := by
    rw [lookupReservedCosted_result]
    exact (List.length_filterMap_le _ _).trans_eq hpSize
  have hb := canonicalLookupSortCosted_cost_le key compare input keyCost hkey
  have ht := canonicalLookupSortCosted_cost_le key compare table keyCost hkey
  have hp : plan.2 = input.length * (equal + 2) + 1 := by
    rw [lookupRunPlanCosted_cost, hbSize]
  have hr : reserved.2 ≤ 2 * input.length + 1 := by
    have h := lookupReservedCosted_cost_le plan.1
    rw [hpSize] at h
    exact h
  have hu : unused.2 ≤ input.length * (2 * (table.length * (equal + 2) + 1) + 2) + 1 := by
    have h := reserveLookupValuesCosted_cost_le equal reserved.1 sortedTable.1
    rw [htSize] at h
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hrSize) 1)
  change b.2 ≤ _ at hb
  change sortedTable.2 ≤ _ at ht
  by_cases hlength : input.length ≠ table.length
  · simp only [lookupSortColumnsCosted, lengthListCosted_result, if_pos hlength, lengthListCosted_cost]
    unfold lookupSortColumnsCostBudget
    nlinarith
  · simp only [lookupSortColumnsCosted, lengthListCosted_result]
    change (if input.length ≠ table.length then
        (none, (lengthListCosted input).2 + (lengthListCosted table).2 + 1 + 1) else
        match unused.1 with
        | none => (none, (lengthListCosted input).2 + (lengthListCosted table).2 + 1 +
            b.2 + sortedTable.2 + plan.2 + reserved.2 + unused.2 + 5 + 1)
        | some remaining =>
          ((fillLookupPlanCosted plan.1 (reverseListCosted remaining).1).1.map (fun t => (b.1, t)),
            (lengthListCosted input).2 + (lengthListCosted table).2 + 1 + b.2 + sortedTable.2 +
            plan.2 + reserved.2 + unused.2 + 5 + (reverseListCosted remaining).2 +
            (fillLookupPlanCosted plan.1 (reverseListCosted remaining).1).2 + 3)).2 ≤ _
    rw [if_neg hlength]
    cases hout : unused.1 with
    | none =>
      simp only [lengthListCosted_cost]
      unfold lookupSortColumnsCostBudget
      nlinarith
    | some remaining =>
      have hremaining : remaining.length ≤ table.length := by
        have h := reserveLookupValuesCosted_remaining_length equal reserved.1 sortedTable.1 remaining hout
        rw [htSize] at h
        exact h
      have hfill := fillLookupPlanCosted_cost_le plan.1 (reverseListCosted remaining).1
      rw [hpSize] at hfill
      simp only [lengthListCosted_cost, reverseListCosted_cost]
      unfold lookupSortColumnsCostBudget
      nlinarith

end Zcash.Snark.ZeroKnowledge
