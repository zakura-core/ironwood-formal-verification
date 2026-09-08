import Zcash.Snark.ZeroKnowledge.AdviceAliasInvariant
import Zcash.Snark.ZeroKnowledge.WitnessProgramSupport
import Zcash.Circuits.Ecc.MulIncompleteRound

/-!
# Native copies in Action's shared scalar-multiplication columns

Both incomplete multiplication halves write the same base-point columns. The
base-coordinate callbacks in the original program are copies: the scalar bits
and accumulator arithmetic do not affect those two outputs. These equalities
hold for every environment, including exceptional arithmetic values.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2
open Zcash.Circuits.Ecc

/-- The original native x-coordinate callback copies the preceding base x cell exactly. -/
theorem mulIncomplete_stepWit_baseX_copy
    (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (state : MulIncomplete.State (AssignedCell Fp)) (bit : ℕ)
    (environment : Placed ProverEnvironment Fp) :
    ((MulIncomplete.stepWit alpha state bit (·.base.x)).eval environment)[0] =
      state.base.x.eval environment.place environment.env.toEnvironment := by
  rw [MulIncomplete.stepWit_eval]
  rfl

/-- The original native y-coordinate callback copies the preceding base y cell exactly. -/
theorem mulIncomplete_stepWit_baseY_copy
    (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (state : MulIncomplete.State (AssignedCell Fp)) (bit : ℕ)
    (environment : Placed ProverEnvironment Fp) :
    ((MulIncomplete.stepWit alpha state bit (·.base.y)).eval environment)[0] =
      state.base.y.eval environment.place environment.env.toEnvironment := by
  rw [MulIncomplete.stepWit_eval]
  rfl

/-- The native base-x write has the exact source semantics consumed by the alias certificate. -/
theorem mulIncomplete_baseX_copySemantics (place : RegionIndex → ℕ)
    (column : Column .advice) (row : ℕ)
    (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (state : MulIncomplete.State (AssignedCell Fp)) (bit : ℕ) :
    AdviceCopySemantics place ⟨column, row, MulIncomplete.stepWit alpha state bit (·.base.x)⟩
      (placedWitnessCell place state.base.x) := by
  intro environment
  exact mulIncomplete_stepWit_baseX_copy alpha state bit ⟨place, environment⟩

/-- The native base-y write has the exact source semantics consumed by the alias certificate. -/
theorem mulIncomplete_baseY_copySemantics (place : RegionIndex → ℕ)
    (column : Column .advice) (row : ℕ)
    (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (state : MulIncomplete.State (AssignedCell Fp)) (bit : ℕ) :
    AdviceCopySemantics place ⟨column, row, MulIncomplete.stepWit alpha state bit (·.base.y)⟩
      (placedWitnessCell place state.base.y) := by
  intro environment
  exact mulIncomplete_stepWit_baseY_copy alpha state bit ⟨place, environment⟩

end Zcash.Snark.ZeroKnowledge
