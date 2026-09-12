import Zcash.Snark.ZeroKnowledge.LookupPlanCost
import Zcash.Snark.ZeroKnowledge.ListTraversalCost

/-!
# A counted implementation of the complete canonical lookup sorter

The comparison sort has a conservative quadratic bound. Injectivity of the
canonical key proves exact equality with the reference merge-sort result; both
therefore feed the same reservation and reverse-fill algorithm. Key extraction,
comparisons, input-length checks, and all failing branches retain their costs.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {A : Type*}

/-- Insert into a sorted list, charging the complete key extraction and comparison costs. -/
def lookupInsertCosted (key : A → ℕ × ℕ) (compare : ℕ) (value : A) : List A → List A × ℕ
  | [] => ([value], 2)
  | first :: rest =>
    let left := key value
    let right := key first
    if left.1 ≤ right.1 then (value :: first :: rest, left.2 + right.2 + compare + 3) else
      let tail := lookupInsertCosted key compare value rest
      (first :: tail.1, left.2 + right.2 + compare + tail.2 + 3)

/-- The counted insertion returns the ordinary ordered insertion. -/
theorem lookupInsertCosted_result (key : A → ℕ × ℕ) (compare : ℕ) (value : A) (values : List A) :
    (lookupInsertCosted key compare value values).1 =
      values.orderedInsert (fun left right => (key left).1 ≤ (key right).1) value := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simp only [lookupInsertCosted, List.orderedInsert_cons]
    split <;> simp_all only

/-- Every insertion retains both key prices on every comparison along its path. -/
theorem lookupInsertCosted_cost_le (key : A → ℕ × ℕ) (compare : ℕ) (value : A)
    (values : List A) (keyCost : ℕ) (hkey : ∀ value, (key value).2 ≤ keyCost) :
    (lookupInsertCosted key compare value values).2 ≤
      values.length * (2 * keyCost + compare + 3) + 2 := by
  induction values with
  | nil => simp [lookupInsertCosted]
  | cons first rest ih =>
    have hleft := hkey value
    have hright := hkey first
    simp only [lookupInsertCosted, List.length_cons, Nat.add_mul, Nat.one_mul]
    split <;> omega

/-- Materialize a canonical comparison sort with explicit insertion costs. -/
def canonicalLookupSortCosted (key : A → ℕ × ℕ) (compare : ℕ) : List A → List A × ℕ
  | [] => ([], 1)
  | first :: rest =>
    let tail := canonicalLookupSortCosted key compare rest
    let inserted := lookupInsertCosted key compare first tail.1
    (inserted.1, tail.2 + inserted.2 + 1)

/-- Erasure is the standard insertion sort by the supplied canonical key. -/
theorem canonicalLookupSortCosted_insertionSort (key : A → ℕ × ℕ) (compare : ℕ) (values : List A) :
    (canonicalLookupSortCosted key compare values).1 =
      values.insertionSort (fun left right => (key left).1 ≤ (key right).1) := by
  induction values <;>
    simp_all only [canonicalLookupSortCosted, lookupInsertCosted_result,
      List.insertionSort_nil, List.insertionSort_cons]

/-- The counted sort materializes exactly one cell for each input value. -/
theorem canonicalLookupSortCosted_length (key : A → ℕ × ℕ) (compare : ℕ) (values : List A) :
    (canonicalLookupSortCosted key compare values).1.length = values.length := by
  rw [canonicalLookupSortCosted_insertionSort, List.length_insertionSort]

/-- Injective canonical keys identify exactly the reference merge-sort output, including duplicates. -/
theorem canonicalLookupSortCosted_result (key : A → ℕ × ℕ) (compare : ℕ) (values : List A)
    (hkey : Function.Injective (fun value => (key value).1)) :
    (canonicalLookupSortCosted key compare values).1 = canonicalLookupSort (fun value => (key value).1) values := by
  let relation := fun left right : A => (key left).1 ≤ (key right).1
  letI : Std.Total relation := ⟨fun left right => Nat.le_total _ _⟩
  letI : IsTrans A relation := ⟨fun _ _ _ => Nat.le_trans⟩
  letI : Std.Antisymm relation := ⟨fun _ _ hlr hrl => hkey (Nat.le_antisymm hlr hrl)⟩
  rw [canonicalLookupSortCosted_insertionSort]
  exact (List.mergeSort_eq_insertionSort relation values).symm

/-- A polynomial bound on the complete comparison sort, with every callback price retained. -/
theorem canonicalLookupSortCosted_cost_le (key : A → ℕ × ℕ) (compare : ℕ) (values : List A)
    (keyCost : ℕ) (hkey : ∀ value, (key value).2 ≤ keyCost) :
    (canonicalLookupSortCosted key compare values).2 ≤
      values.length ^ 2 * (2 * keyCost + compare + 6) + 1 := by
  induction values with
  | nil => simp [canonicalLookupSortCosted]
  | cons first rest ih =>
    have h := lookupInsertCosted_cost_le key compare first
      (canonicalLookupSortCosted key compare rest).1 keyCost hkey
    rw [canonicalLookupSortCosted_length] at h
    simp only [canonicalLookupSortCosted, List.length_cons]
    nlinarith

/-- Execute the complete original sorting, reservation, and reverse-fill pipeline. -/
def lookupSortColumnsCosted [DecidableEq A] (key : A → ℕ × ℕ) (compare equal : ℕ)
    (input table : List A) : Option (List A × List A) × ℕ :=
  let inputLength := lengthListCosted input
  let tableLength := lengthListCosted table
  let lengthsCost := inputLength.2 + tableLength.2 + 1
  if inputLength.1 ≠ tableLength.1 then (none, lengthsCost + 1) else
    let b := canonicalLookupSortCosted key compare input
    let sortedTable := canonicalLookupSortCosted key compare table
    let plan := lookupRunPlanCosted equal none b.1
    let reserved := lookupReservedCosted plan.1
    let unused := reserveLookupValuesCosted equal reserved.1 sortedTable.1
    let prefixCost := lengthsCost + b.2 + sortedTable.2 + plan.2 + reserved.2 + unused.2 + 5
    match unused.1 with
    | none => (none, prefixCost + 1)
    | some remaining =>
      let reversed := reverseListCosted remaining
      let filled := fillLookupPlanCosted plan.1 reversed.1
      (filled.1.map (fun t => (b.1, t)), prefixCost + reversed.2 + filled.2 + 3)

/-- Every value and failure flag agrees with the original complete sorter. -/
theorem lookupSortColumnsCosted_result [DecidableEq A] (key : A → ℕ × ℕ) (compare equal : ℕ)
    (input table : List A) (hkey : Function.Injective (fun value => (key value).1)) :
    (lookupSortColumnsCosted key compare equal input table).1 =
      lookupSortColumns (fun value => (key value).1) input table := by
  simp only [lookupSortColumnsCosted, lengthListCosted_result, canonicalLookupSortCosted_result _ _ _ hkey,
    lookupRunPlanCosted_result, lookupReservedCosted_result, reserveLookupValuesCosted_result,
    reverseListCosted_result, fillLookupPlanCosted_result, lookupSortColumns]
  split
  · rfl
  · split <;> simp_all
    exact Option.map_eq_bind

end Zcash.Snark.ZeroKnowledge
