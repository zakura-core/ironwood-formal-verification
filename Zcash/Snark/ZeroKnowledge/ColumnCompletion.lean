import Zcash.Snark.ZeroKnowledge.ColumnAttempt

/-!
# Completion from successful constructors on the total reference path

If every scheduled constructor succeeds on its actual earlier totalized history,
the partial execution follows that same history and completes. This supplies a
way to prove completion from concrete lookup membership without assuming success
or conditioning the tape distribution on it.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Pointwise constructor success along the total path implies completion on the original tape. -/
theorem columnAttemptFromTape_complete_of_total {n : ℕ} (steps : List (ColumnAttemptStep n))
    (history : ColumnHistory n)
    (tape : Fin (columnRowSampleCount (steps.map ColumnAttemptStep.totalize)) → Fp)
    (hready : ∀ j (hj : j < steps.length),
      (steps[j]'hj).rows
        (((columnRowsFromTape (steps.map ColumnAttemptStep.totalize) history tape).take j).reverse ++ history) ≠ none) :
    (columnAttemptFromTape steps history tape).complete = true := by
  induction steps generalizing history with
  | nil => rfl
  | cons step rest ih =>
      have hhead : step.rows history ≠ none := by
        simpa only [List.getElem_cons_zero, List.take_zero, List.reverse_nil, List.nil_append] using
          hready 0 (by simp)
      cases hrows : step.rows history with
      | none => exact False.elim (hhead hrows)
      | some base =>
          let coins := splitTapeEquiv (n - step.firstMasked)
            (columnRowSampleCount (rest.map ColumnAttemptStep.totalize)) Fp tape
          let row := columnRowsFromCoins step.totalize history coins.1
          have htail : ∀ j (hj : j < rest.length),
              (rest[j]'hj).rows
                (((columnRowsFromTape (rest.map ColumnAttemptStep.totalize) (row :: history) coins.2).take j).reverse ++
                  (row :: history)) ≠ none := by
            intro j hj
            simpa only [List.map_cons, columnRowsFromTape, List.getElem_cons_succ,
              List.take_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
              hready (j + 1) (Nat.succ_lt_succ hj)
          simpa only [columnAttemptFromTape, hrows] using ih (row :: history) coins.2 htail

end Zcash.Snark.ZeroKnowledge
