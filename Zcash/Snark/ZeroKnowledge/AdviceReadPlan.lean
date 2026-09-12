import Zcash.Snark.ZeroKnowledge.WitnessProgramSupport

/-!
# Checking structured advice-read order

The Boolean scan checks the collected reads of every structured program against
the cells available at that exact source position. Native programs have explicit
semantic obligations, threaded through the same positions. Combining those
obligations with the successful scan proves the full causal-read certificate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen

/-- A structured cell read is available when it is immutable or was already written. -/
def adviceCellReadAvailable {F : Type} (place : RegionIndex → ℕ)
    (available : List (AnyColumn × ℤ)) (cell : AssignedCell F) : Bool :=
  decide (cell.cell.column.kind ≠ .advice ∨ placedWitnessCell place cell ∈ available)

/-- Check every structured witness read at its original source-order position. -/
def adviceReadPlan {F : Type} (place : RegionIndex → ℕ) : List (AnyColumn × ℤ) →
    List (PlacedAdviceProgram F) → Bool
  | _, [] => true
  | available, instruction :: rest =>
    let step := match instruction.program with
      | .native _ => true
      | .ir steps output =>
        (stepsWitnessReads steps ++ vectorWitnessReads output).all (adviceCellReadAvailable place available)
    step && adviceReadPlan place (adviceProgramTarget instruction :: available) rest

/-- Native callbacks require semantic read certificates at those same source-order positions. -/
def NativeAdviceReads {F : Type} [FiniteField F] (place : RegionIndex → ℕ) :
    List (AnyColumn × ℤ) → List (PlacedAdviceProgram F) → Prop
  | _, [] => True
  | available, instruction :: rest =>
    (match instruction.program with
      | .native _ => AdviceProgramReadsFrom place available instruction.program
      | .ir _ _ => True) ∧
    NativeAdviceReads place (adviceProgramTarget instruction :: available) rest

/-- A successful structured scan and the actual native certificates establish every program's read order. -/
theorem adviceReadPlan_causal {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (PlacedAdviceProgram F)) (available : List (AnyColumn × ℤ))
    (hcheck : adviceReadPlan place available programs = true)
    (hnative : NativeAdviceReads place available programs) :
    AdviceProgramsCausal place available programs := by
  induction programs generalizing available with
  | nil => trivial
  | cons instruction rest ih =>
    obtain ⟨hthisNative, hrestNative⟩ := hnative
    rcases instruction with ⟨column, row, program⟩
    cases program with
    | native callback =>
      simp only [adviceReadPlan, Bool.true_and] at hcheck
      exact ⟨hthisNative, ih _ hcheck hrestNative⟩
    | ir steps output =>
      obtain ⟨hthis, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
      constructor
      · apply structuredWitness_readsFrom
        intro cell hcell hadvice
        have havailable := (List.all_eq_true.mp hthis) cell hcell
        have hread := of_decide_eq_true havailable
        exact hread.resolve_left (by simp [hadvice])
      · exact ih _ hrest hrestNative

end Zcash.Snark.ZeroKnowledge
