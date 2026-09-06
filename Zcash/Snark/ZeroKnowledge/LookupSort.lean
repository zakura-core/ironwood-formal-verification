import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# The pinned lookup sorting and table-fill algorithm

A computable functional model of step 2 in the pinned prover description. Run starts
reserve one matching table occurrence. Repeated-input slots are filled from left to
right using the reversed unused table, which gives the specified highest-row-first
assignment of ascending unused values. Missing occurrences or inconsistent lengths
return `none`.

Successful executions preserve both multisets and satisfy the verifier's first-row
and run-structure rules. This models the specified value order; correspondence with
Rust control flow and emitted error prefixes remains separate.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {A : Type*}

/-- Reserve each run's first row and mark its repeated rows as free slots. -/
def lookupRunPlan [DecidableEq A] (previous : Option A) : List A → List (Option A)
  | [] => []
  | a :: rest => (if previous = some a then none else some a) :: lookupRunPlan (some a) rest

/-- Remove the first remaining occurrence of each reserved value, failing if one is absent. -/
def reserveLookupValues [DecidableEq A] : List A → List A → Option (List A)
  | [], table => some table
  | a :: rest, table => if a ∈ table then reserveLookupValues rest (table.erase a) else none

/-- Fill free slots in row order, using exactly the supplied unused values. -/
def fillLookupPlan : List (Option A) → List A → Option (List A)
  | [], [] => some []
  | [], _ :: _ => none
  | some a :: rest, unused => (fillLookupPlan rest unused).map (List.cons a)
  | none :: rest, a :: unused => (fillLookupPlan rest unused).map (List.cons a)
  | none :: _, [] => none

/-- Sort by the supplied canonical integer key. -/
def canonicalLookupSort (key : A → ℕ) (values : List A) : List A :=
  values.mergeSort (fun a b => decide (key a ≤ key b))

/-- Compute both permuted prefixes, with the prescribed reverse fill order. -/
def lookupSortColumns [DecidableEq A] (key : A → ℕ) (input table : List A) : Option (List A × List A) := do
  if input.length ≠ table.length then none else do
    let b := canonicalLookupSort key input
    let sortedTable := canonicalLookupSort key table
    let plan := lookupRunPlan none b
    let unused ← reserveLookupValues (plan.filterMap id) sortedTable
    let t ← fillLookupPlan plan unused.reverse
    some (b, t)

/-- The reservation plan has one slot per input row. -/
theorem lookupRunPlan_length [DecidableEq A] (previous : Option A) (input : List A) :
    (lookupRunPlan previous input).length = input.length := by
  induction input generalizing previous with
  | nil => rfl
  | cons a rest ih => simp [lookupRunPlan, ih]

/-- Canonical sorting preserves the input multiset. -/
theorem canonicalLookupSort_perm (key : A → ℕ) (values : List A) :
    (canonicalLookupSort key values).Perm values := List.mergeSort_perm _ _

/-- Canonical sorting puts the integer keys in nondecreasing order. -/
theorem canonicalLookupSort_ordered (key : A → ℕ) (values : List A) :
    (canonicalLookupSort key values).Pairwise (fun a b => key a ≤ key b) := by
  simpa only [canonicalLookupSort, decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
      (fun a b c hab hbc => by simpa using Nat.le_trans (by simpa using hab) (by simpa using hbc))
      (fun a b => by simpa using Nat.le_total (key a) (key b)) values

/-- A prefix already in canonical order is unchanged; equal keys identify equal values. -/
theorem canonicalLookupSort_eq_of_ordered (key : A → ℕ) (hkey : Function.Injective key)
    (values : List A) (hsorted : values.Pairwise (fun a b => key a ≤ key b)) :
    canonicalLookupSort key values = values := by
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => hkey (Nat.le_antisymm hab hba))
    (canonicalLookupSort_ordered key values) hsorted (canonicalLookupSort_perm key values)

/-- A slot is free exactly when its value repeats the preceding input value. -/
theorem lookupRunPlan_getElem [DecidableEq A] (previous : Option A) (input : List A)
    (i : ℕ) (hi : i < input.length) :
    (lookupRunPlan previous input)[i]'(by simpa only [lookupRunPlan_length] using hi) =
      if (if i = 0 then previous else input[i - 1]?) = some input[i] then none else some input[i] := by
  induction input generalizing previous i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      change (lookupRunPlan (some a) rest)[i]'(by simpa only [lookupRunPlan_length] using hi') =
        if (a :: rest)[i]? = some rest[i] then none else some rest[i]
      rw [ih (some a) i hi']
      cases i <;> rfl

/-- A filled row either repeats its predecessor or matches its reserved table value. -/
theorem lookupRunPlan_matches [DecidableEq A] (previous : Option A) (input output : List A)
    (hmatch : List.Forall₂ (fun entry value => entry = none ∨ entry = some value)
      (lookupRunPlan previous input) output) (i : ℕ) (hi : i < input.length) :
    (if i = 0 then previous else input[i - 1]?) = some input[i] ∨
      input[i] = output[i]'(by rw [← hmatch.length_eq, lookupRunPlan_length]; exact hi) := by
  have hrow := hmatch.get (i := i) (by simpa only [lookupRunPlan_length] using hi)
    (by rw [← hmatch.length_eq, lookupRunPlan_length]; exact hi)
  simp only [List.get_eq_getElem] at hrow
  rw [lookupRunPlan_getElem previous input i hi] at hrow
  by_cases hrepeat : (if i = 0 then previous else input[i - 1]?) = some input[i]
  · exact Or.inl hrepeat
  · simp only [if_neg hrepeat, Option.some_ne_none, false_or, Option.some.injEq] at hrow
    exact Or.inr hrow

/-- Successful reservation accounts for every original table occurrence. -/
theorem reserveLookupValues_perm [DecidableEq A] (reserved table unused : List A)
    (h : reserveLookupValues reserved table = some unused) :
    (reserved ++ unused).Perm table := by
  induction reserved generalizing table with
  | nil =>
    simp only [reserveLookupValues, Option.some.injEq] at h
    subst table
    exact List.Perm.refl _
  | cons a rest ih =>
    by_cases ha : a ∈ table
    · rw [reserveLookupValues, if_pos ha] at h
      exact ((ih (table.erase a) h).cons a).trans (List.perm_cons_erase ha).symm
    · simp [reserveLookupValues, ha] at h

/-- Filling uses each supplied value exactly once and preserves every reservation. -/
theorem fillLookupPlan_correct (plan : List (Option A)) (unused output : List A)
    (h : fillLookupPlan plan unused = some output) :
    (plan.filterMap id ++ unused).Perm output ∧
      List.Forall₂ (fun entry value => entry = none ∨ entry = some value) plan output := by
  induction plan generalizing unused output with
  | nil =>
    cases unused with
    | nil =>
      simp only [fillLookupPlan, Option.some.injEq] at h
      subst output
      exact ⟨List.Perm.refl _, List.Forall₂.nil⟩
    | cons a rest => simp [fillLookupPlan] at h
  | cons entry rest ih =>
    cases entry with
    | none =>
      cases unused with
      | nil => simp [fillLookupPlan] at h
      | cons a unused =>
        change (fillLookupPlan rest unused).map (List.cons a) = some output at h
        obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hperm, hmatch⟩ := ih unused tail htail
        exact ⟨List.perm_middle.trans (hperm.cons a),
          List.Forall₂.cons (Or.inl rfl) hmatch⟩
    | some a =>
      change (fillLookupPlan rest unused).map (List.cons a) = some output at h
      obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hperm, hmatch⟩ := ih unused tail htail
      exact ⟨hperm.cons a, List.Forall₂.cons (Or.inr rfl) hmatch⟩

/-- Successful output preserves both multisets and obeys its reservation plan. -/
theorem lookupSortColumns_correct [DecidableEq A] (key : A → ℕ)
    (input table b t : List A) (h : lookupSortColumns key input table = some (b, t)) :
    b.Perm input ∧ t.Perm table ∧
      List.Forall₂ (fun entry value => entry = none ∨ entry = some value) (lookupRunPlan none b) t := by
  unfold lookupSortColumns at h
  split at h
  · contradiction
  · dsimp only at h
    obtain ⟨unused, hreserve, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨output, hfill, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hperm, hmatch⟩ := fillLookupPlan_correct _ _ _ hfill
    refine ⟨canonicalLookupSort_perm key input, ?_, hmatch⟩
    exact hperm.symm.trans (((List.Perm.refl _).append (List.reverse_perm unused)).trans
      ((reserveLookupValues_perm _ _ _ hreserve).trans (canonicalLookupSort_perm key table)))

/-- The first permuted input and table entries agree, including the empty-prefix case. -/
theorem lookupSortColumns_first [DecidableEq A] (key : A → ℕ)
    (input table b t : List A) (fallback : A) (h : lookupSortColumns key input table = some (b, t)) :
    b.getD 0 fallback = t.getD 0 fallback := by
  have hmatch := (lookupSortColumns_correct key input table b t h).2.2
  have hlen : b.length = t.length := (lookupRunPlan_length none b).symm.trans hmatch.length_eq
  by_cases hb : 0 < b.length
  · have ht : 0 < t.length := by omega
    rw [List.getD_eq_getElem b fallback hb, List.getD_eq_getElem t fallback ht]
    have hrow := lookupRunPlan_matches none b t hmatch 0 hb
    simpa using hrow
  · rw [List.getD_eq_default b fallback (by omega), List.getD_eq_default t fallback (by omega)]

/-- Each later input value matches its table row or repeats its preceding input value. -/
theorem lookupSortColumns_run [DecidableEq A] (key : A → ℕ)
    (input table b t : List A) (fallback : A) (h : lookupSortColumns key input table = some (b, t))
    (i : ℕ) (hpos : 0 < i) (hi : i < b.length) :
    b.getD i fallback = t.getD i fallback ∨ b.getD i fallback = b.getD (i - 1) fallback := by
  have hmatch := (lookupSortColumns_correct key input table b t h).2.2
  have hlen : b.length = t.length := (lookupRunPlan_length none b).symm.trans hmatch.length_eq
  have ht : i < t.length := by omega
  rcases lookupRunPlan_matches none b t hmatch i hi with hrepeat | heq
  · rw [if_neg (by omega : i ≠ 0)] at hrepeat
    obtain ⟨hprev, hprevEq⟩ := List.getElem?_eq_some_iff.mp hrepeat
    right
    rw [List.getD_eq_getElem b fallback hi, List.getD_eq_getElem b fallback hprev]
    exact hprevEq.symm
  · left
    rw [List.getD_eq_getElem b fallback hi, List.getD_eq_getElem t fallback ht]
    exact heq

/-- Reading all valid positions reconstructs the list, independently of the fallback. -/
theorem ofFn_getD_eq (values : List A) (fallback : A) :
    List.ofFn (fun i : Fin values.length => values.getD i.val fallback) = values := by
  have hfun : (fun i : Fin values.length => values.getD i.val fallback) = values.get := by
    funext i
    exact List.getD_eq_get values fallback i
  rw [hfun, List.ofFn_get]

end Zcash.Snark.ZeroKnowledge
