import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Snark.ZeroKnowledge.ActionNativeCopies
import Zcash.Circuits.Ecc.MulIncomplete

/-!
# Read certificates for the original incomplete-multiplication callbacks

The general state callbacks depend on the six entering cells and, for a step,
the scalar builder. The shared base-coordinate writes have the stronger support
of just their copied cell, using the already proved exact copy semantics.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen
open Zcash.Circuits
open Zcash.Circuits.Ecc

/-- The six cells read by the original incomplete-multiplication state evaluator. -/
def mulIncompleteStateReads (state : MulIncomplete.State (AssignedCell Fp)) : List (AssignedCell Fp) :=
  [state.z, state.xA, state.lambda1, state.lambda2, state.base.x, state.base.y]

/-- Equal entering cell values determine the entire state record. -/
theorem mulIncomplete_readsValue_support (state : MulIncomplete.State (AssignedCell Fp)) :
    WitnessFunctionSupport (mulIncompleteStateReads state) (MulIncomplete.readsValue state) := by
  intro left right agreement
  have hz : readCell left state.z = readCell right state.z :=
    agreement.cellValues state.z (by simp [mulIncompleteStateReads])
  have hx : readCell left state.xA = readCell right state.xA :=
    agreement.cellValues state.xA (by simp [mulIncompleteStateReads])
  have h1 : readCell left state.lambda1 = readCell right state.lambda1 :=
    agreement.cellValues state.lambda1 (by simp [mulIncompleteStateReads])
  have h2 : readCell left state.lambda2 = readCell right state.lambda2 :=
    agreement.cellValues state.lambda2 (by simp [mulIncompleteStateReads])
  have hbx : readCell left state.base.x = readCell right state.base.x :=
    agreement.cellValues state.base.x (by simp [mulIncompleteStateReads])
  have hby : readCell left state.base.y = readCell right state.base.y :=
    agreement.cellValues state.base.y (by simp [mulIncompleteStateReads])
  simp only [MulIncomplete.readsValue, hz, hx, h1, h2, hbx, hby]

/-- Any original state projection or final-coordinate computation has this support. -/
theorem mulIncomplete_readWit_support (state : MulIncomplete.State (AssignedCell Fp))
    (f : MulIncomplete.State Fp → Fp) :
    WitnessFunctionSupport (mulIncompleteStateReads state)
      (fun env => ((MulIncomplete.readWit state f).eval env)[0]) := by
  intro left right agreement
  simp only [MulIncomplete.readWit_eval,
    mulIncomplete_readsValue_support state left right agreement]

/-- A native step depends only on its entering state and the actual scalar builder. -/
theorem mulIncomplete_stepWit_support (alpha : MOver Fp (AssignedCell Fp) (FExpr Fp))
    (state : MulIncomplete.State (AssignedCell Fp)) (bit : ℕ) (f : MulIncomplete.State Fp → Fp) :
    WitnessFunctionSupport (mulIncompleteStateReads state ++ valueBuilderReads (value := field) alpha)
      (fun env => ((MulIncomplete.stepWit alpha state bit f).eval env)[0]) := by
  intro left right agreement
  have hstate := mulIncomplete_readsValue_support state left right agreement.left
  have halpha := valueBuilderReads_eval (value := field) alpha left right agreement.right
  simp only [MulIncomplete.stepWit_eval, MulIncomplete.bitWit, hstate, halpha]

/-- Base-x writes need only their source cell, even when other state inputs change. -/
theorem mulIncomplete_stepWit_baseX_support (alpha : MOver Fp (AssignedCell Fp) (FExpr Fp))
    (state : MulIncomplete.State (AssignedCell Fp)) (bit : ℕ) :
    WitnessFunctionSupport [state.base.x]
      (fun env => ((MulIncomplete.stepWit alpha state bit (·.base.x)).eval env)[0]) := by
  intro left right agreement
  simpa only [mulIncomplete_stepWit_baseX_copy] using
    agreement.cellValues state.base.x (List.mem_singleton_self _)

/-- Base-y writes likewise need only their source cell. -/
theorem mulIncomplete_stepWit_baseY_support (alpha : MOver Fp (AssignedCell Fp) (FExpr Fp))
    (state : MulIncomplete.State (AssignedCell Fp)) (bit : ℕ) :
    WitnessFunctionSupport [state.base.y]
      (fun env => ((MulIncomplete.stepWit alpha state bit (·.base.y)).eval env)[0]) := by
  intro left right agreement
  simpa only [mulIncomplete_stepWit_baseY_copy] using
    agreement.cellValues state.base.y (List.mem_singleton_self _)

/-- The original initial slopes read the base, accumulator, and scalar builder. -/
theorem mulIncomplete_initLambdaWit_support (alpha : MOver Fp (AssignedCell Fp) (FExpr Fp))
    (base acc : Point (AssignedCell Fp)) (bit : ℕ)
    (f : Ecc.Mul.Incomplete.DoubleAndAdd.LambdaCells Fp → Fp) :
    WitnessFunctionSupport ([base.x, base.y, acc.x, acc.y] ++ valueBuilderReads (value := field) alpha)
      (fun env => ((MulIncomplete.initLambdaWit alpha base acc bit f).eval env)[0]) := by
  intro left right agreement
  have hbx : readCell left base.x = readCell right base.x := agreement.left.cellValues base.x (by simp)
  have hby : readCell left base.y = readCell right base.y := agreement.left.cellValues base.y (by simp)
  have hax : readCell left acc.x = readCell right acc.x := agreement.left.cellValues acc.x (by simp)
  have hay : readCell left acc.y = readCell right acc.y := agreement.left.cellValues acc.y (by simp)
  have halpha := valueBuilderReads_eval (value := field) alpha left right agreement.right
  simp only [MulIncomplete.initLambdaWit_eval, MulIncomplete.bitWit, hbx, hby, hax, hay, halpha]

end Zcash.Snark.ZeroKnowledge
