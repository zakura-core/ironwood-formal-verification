import Zcash.Snark.ZeroKnowledge.ColumnSequence

/-!
# Column construction with an explicit failure outcome

A partial retained-row constructor may stop before a column is masked. The result
retains the successfully constructed prefix, in emission order. These are private
row vectors, not a claim that their contents are disclosed to the verifier.

The supplied tape reserves the full schedule's row masks. A failed attempt leaves
its unused suffix unread. Totalizing a failed constructor to zero is useful only
for connecting to the existing joint simulation: successful attempts agree exactly,
and failed attempts retain exactly a prefix of that totalized computation. Failure
probabilities and the actual emitted messages still need a separate simulation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- One retained-row construction that can fail before applying its fresh suffix mask. -/
structure ColumnAttemptStep (n : ℕ) where
  firstMasked : ℕ
  rows : ColumnHistory n → Option (Fin n → Fp)

/-- A total constructor for the comparison experiment; failure is replaced by zero rows. -/
def ColumnAttemptStep.totalize {n : ℕ} (step : ColumnAttemptStep n) : ColumnStep n :=
  ⟨step.firstMasked, fun history => (step.rows history).getD 0⟩

/-- The private prefix constructed before failure, or all columns on completion. -/
structure ColumnAttemptResult (n : ℕ) where
  columns : ColumnHistory n
  complete : Bool

/-- Execute the partial schedule, retaining its prefix and stopping at the first failure. -/
def columnAttemptFromTape {n : ℕ} : (steps : List (ColumnAttemptStep n)) → ColumnHistory n →
    (Fin (columnRowSampleCount (steps.map ColumnAttemptStep.totalize)) → Fp) → ColumnAttemptResult n
  | [], _, _ => ⟨[], true⟩
  | step :: rest, history, tape =>
    match step.rows history with
    | none => ⟨[], false⟩
    | some _ =>
      let coins := splitTapeEquiv (n - step.firstMasked)
        (columnRowSampleCount (rest.map ColumnAttemptStep.totalize)) Fp tape
      let row := columnRowsFromCoins step.totalize history coins.1
      let later := columnAttemptFromTape rest (row :: history) coins.2
      ⟨row :: later.columns, later.complete⟩

/-- An attempt constructs at most the declared number of columns. -/
theorem columnAttemptFromTape_length_le {n : ℕ} (steps : List (ColumnAttemptStep n))
    (history : ColumnHistory n)
    (tape : Fin (columnRowSampleCount (steps.map ColumnAttemptStep.totalize)) → Fp) :
    (columnAttemptFromTape steps history tape).columns.length ≤ steps.length := by
  induction steps generalizing history with
  | nil => simp [columnAttemptFromTape]
  | cons step rest ih =>
    cases hrows : step.rows history with
    | none => simp [columnAttemptFromTape, hrows]
    | some rows => simpa [columnAttemptFromTape, hrows] using Nat.succ_le_succ (ih _ _)

/-- Completion means that every declared column was constructed. -/
theorem columnAttemptFromTape_complete_iff {n : ℕ} (steps : List (ColumnAttemptStep n))
    (history : ColumnHistory n)
    (tape : Fin (columnRowSampleCount (steps.map ColumnAttemptStep.totalize)) → Fp) :
    (columnAttemptFromTape steps history tape).complete = true ↔
      (columnAttemptFromTape steps history tape).columns.length = steps.length := by
  induction steps generalizing history with
  | nil => simp [columnAttemptFromTape]
  | cons step rest ih =>
    cases hrows : step.rows history with
    | none => simp [columnAttemptFromTape, hrows]
    | some rows => simpa [columnAttemptFromTape, hrows] using ih _ _

/-- Every successful prefix is exactly the corresponding prefix of the total comparison run. -/
theorem columnAttemptFromTape_eq_take {n : ℕ} (steps : List (ColumnAttemptStep n))
    (history : ColumnHistory n)
    (tape : Fin (columnRowSampleCount (steps.map ColumnAttemptStep.totalize)) → Fp) :
    (columnAttemptFromTape steps history tape).columns =
      (columnRowsFromTape (steps.map ColumnAttemptStep.totalize) history tape).take
        (columnAttemptFromTape steps history tape).columns.length := by
  induction steps generalizing history with
  | nil => rfl
  | cons step rest ih =>
    cases hrows : step.rows history with
    | none => simp [columnAttemptFromTape, hrows]
    | some rows =>
      simpa only [columnAttemptFromTape, hrows, List.map_cons, columnRowsFromTape,
        ColumnAttemptStep.totalize, List.length_cons, List.take_succ_cons, List.cons.injEq,
        true_and] using ih _ _

/-- Successful attempts agree with the entire totalized run on the same tape. -/
theorem columnAttemptFromTape_eq_of_complete {n : ℕ} (steps : List (ColumnAttemptStep n))
    (history : ColumnHistory n)
    (tape : Fin (columnRowSampleCount (steps.map ColumnAttemptStep.totalize)) → Fp)
    (hcomplete : (columnAttemptFromTape steps history tape).complete = true) :
    (columnAttemptFromTape steps history tape).columns =
      columnRowsFromTape (steps.map ColumnAttemptStep.totalize) history tape := by
  rw [columnAttemptFromTape_eq_take,
    (columnAttemptFromTape_complete_iff steps history tape).mp hcomplete]
  have hlength := columnRowsFromTape_length (steps.map ColumnAttemptStep.totalize) history tape
  rw [List.length_map] at hlength
  rw [← hlength, List.take_length]

/-- On a successful construction, the suffix mask leaves all retained rows unchanged. -/
theorem ColumnAttemptStep.retained {n : ℕ} (step : ColumnAttemptStep n)
    (history : ColumnHistory n) (rows : Fin n → Fp) (hrows : step.rows history = some rows)
    (tape : Fin (n - step.firstMasked) → Fp) (i : Fin n) (hi : i.val < step.firstMasked) :
    columnRowsFromCoins step.totalize history tape i = rows i := by
  change maskedRows step.firstMasked ((step.rows history).getD 0)
    (rowMaskTapeEquiv n step.firstMasked tape) i = rows i
  rw [maskedRows_before _ _ i hi, hrows]
  rfl

/-- Every constructed column uses its actual earlier masked prefix and preserves its retained rows.

This applies also to the prefix of a failed attempt. No premise about the constructor's
dependence on previously disclosed evaluations is required. -/
theorem columnAttemptFromTape_retained {n : ℕ} (steps : List (ColumnAttemptStep n))
    (history : ColumnHistory n)
    (tape : Fin (columnRowSampleCount (steps.map ColumnAttemptStep.totalize)) → Fp)
    (j : ℕ) (hj : j < (columnAttemptFromTape steps history tape).columns.length) :
    ∃ base, (steps[j]'(lt_of_lt_of_le hj (columnAttemptFromTape_length_le steps history tape))).rows
        (((columnAttemptFromTape steps history tape).columns.take j).reverse ++ history) = some base ∧
      ∀ i : Fin n,
        i.val < (steps[j]'(lt_of_lt_of_le hj (columnAttemptFromTape_length_le steps history tape))).firstMasked →
        ((columnAttemptFromTape steps history tape).columns.getD j 0) i = base i := by
  induction steps generalizing history j with
  | nil => simp [columnAttemptFromTape] at hj
  | cons step rest ih =>
    cases hrows : step.rows history with
    | none => simp [columnAttemptFromTape, hrows] at hj
    | some base =>
      let coins := splitTapeEquiv (n - step.firstMasked)
        (columnRowSampleCount (rest.map ColumnAttemptStep.totalize)) Fp tape
      let row := columnRowsFromCoins step.totalize history coins.1
      cases j with
      | zero =>
        refine ⟨base, ?_, ?_⟩
        · simpa only [List.getElem_cons_zero, List.take_zero, List.reverse_nil, List.nil_append] using hrows
        · intro i hi
          simpa [columnAttemptFromTape, hrows] using
            step.retained history base hrows coins.1 i hi
      | succ j =>
        have hj' : j < (columnAttemptFromTape rest (row :: history) coins.2).columns.length := by
          simpa only [columnAttemptFromTape, hrows, List.length_cons, Nat.succ_lt_succ_iff] using hj
        obtain ⟨base', hb, hr⟩ := ih (row :: history) coins.2 j hj'
        refine ⟨base', ?_, ?_⟩
        · simpa only [columnAttemptFromTape, hrows, List.getElem_cons_succ,
            List.take_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using hb
        · intro i hi
          simpa [columnAttemptFromTape, hrows] using hr i hi

end Zcash.Snark.ZeroKnowledge
