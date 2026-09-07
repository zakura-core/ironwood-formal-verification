import Zcash.Snark.ZeroKnowledge.ColumnSequence

/-!
# Earlier columns do not depend on later construction steps

Two executions with the same initial history, construction prefix, and tape entries
in corresponding positions produce the same column prefix. Their later steps and
total tape lengths may differ. This gives a pointwise causality statement before
any distribution or independence assumption is introduced.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Equal construction prefixes and matching tape positions give equal column prefixes. -/
theorem columnRowsFromTape_take_congr {n : ℕ} (cut : ℕ)
    (steps steps' : List (ColumnStep n)) (history : ColumnHistory n)
    (tape : Fin (columnRowSampleCount steps) → Fp)
    (tape' : Fin (columnRowSampleCount steps') → Fp)
    (hsteps : steps.take cut = steps'.take cut)
    (htape : ∀ i j, i.val = j.val → tape i = tape' j) :
    (columnRowsFromTape steps history tape).take cut =
      (columnRowsFromTape steps' history tape').take cut := by
  induction cut generalizing steps steps' history with
  | zero => rfl
  | succ cut ih =>
    cases steps with
    | nil =>
      cases steps' with
      | nil => rfl
      | cons step' rest' => simp at hsteps
    | cons step rest =>
      cases steps' with
      | nil => simp at hsteps
      | cons step' rest' =>
        obtain ⟨rfl, hrest⟩ := List.cons.inj (by simpa using hsteps)
        have hhead :
            (splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest) Fp tape).1 =
              (splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest') Fp tape').1 := by
          funext i
          exact htape _ _ rfl
        have htail : ∀ i : Fin (columnRowSampleCount rest),
            ∀ j : Fin (columnRowSampleCount rest'), i.val = j.val →
              (splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest) Fp tape).2 i =
                (splitTapeEquiv (n - step.firstMasked) (columnRowSampleCount rest') Fp tape').2 j := by
          intro i j hij
          exact htape _ _ (congrArg ((n - step.firstMasked) + ·) hij)
        simp only [columnRowsFromTape, List.take_succ_cons]
        rw [hhead]
        exact congrArg (List.cons _) (ih rest rest' _ _ _ hrest htail)

/-- A proved tape-length equality preserves the uniform sequential construction law. -/
theorem uniformTapeColumnRows_cast {n count : ℕ} (steps : List (ColumnStep n))
    (hcount : columnRowSampleCount steps = count) (history : ColumnHistory n) :
    (PMF.uniformOfFintype (Fin count → Fp)).map
        (fun tape => columnRowsFromTape steps history (tape ∘ Fin.cast hcount)) =
      idealColumnRows steps history := by
  subst count
  exact uniformTapeColumnRows steps history

end Zcash.Snark.ZeroKnowledge
