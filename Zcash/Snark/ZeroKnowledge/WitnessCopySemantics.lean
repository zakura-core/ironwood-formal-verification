import Zcash.Snark.ZeroKnowledge.AdviceAliasInvariant
import Zcash.Snark.ZeroKnowledge.WitnessProgramSupport

/-!
# Recognizing actual copy witness programs

The recognizer accepts only the original single-expression IR copy. Its semantic
proof relates the returned cell to the actual evaluator; failure to recognize a
program makes no claim about that program. Native copies have separate proofs.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen

/-- Recognize a direct cell copy in the actual scalar witness IR. -/
def witnessCopyCell {F : Type} (program : WitgenIR F 1) : Option (AssignedCell F) :=
  match program with
  | .ir [] (.lit expressions) =>
    match expressions[0] with
    | .expr cell => some cell
    | _ => none
  | _ => none

/-- Every recognized copy evaluates to its reported source cell in every environment. -/
theorem witnessCopyCell_eval {F : Type} [FiniteField F]
    (program : WitgenIR F 1) (cell : AssignedCell F) (hcopy : witnessCopyCell program = some cell)
    (environment : Placed ProverEnvironment F) :
    (program.eval environment)[0] = cell.eval environment.place environment.env.toEnvironment := by
  unfold witnessCopyCell at hcopy
  split at hcopy
  · split at hcopy
    · cases Option.some.inj hcopy
      simp_all only [WitgenIROver.eval, VExprOver.eval, Vector.getElem_map, evalSteps,
        FExprOver.eval, WitgenEnv.readVar_halo2]
    · cases hcopy
  · cases hcopy

/-- Resolve a recognized copy through the same placement used by witness execution. -/
def witnessCopyAddress {F : Type} (place : RegionIndex → ℕ)
    (program : WitgenIR F 1) : Option AdviceAddress :=
  (witnessCopyCell program).map (placedWitnessCell place)

/-- A recognized source address supplies the alias verifier's actual-program copy certificate. -/
theorem witnessCopyAddress_semantics {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (instruction : PlacedAdviceProgram F) (source : AdviceAddress)
    (hcopy : witnessCopyAddress place instruction.program = some source) :
    AdviceCopySemantics place instruction source := by
  obtain ⟨cell, hcell, rfl⟩ := Option.map_eq_some_iff.mp hcopy
  intro environment
  exact witnessCopyCell_eval instruction.program cell hcell ⟨place, environment⟩

end Zcash.Snark.ZeroKnowledge
