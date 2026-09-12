import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.Ecc.MulComplete

/-!
# Read support for complete-multiplication witness wrappers

The scalar and signed-coordinate wrappers retain the complete reads of their
structured builders, including a bit-family builder that has not been reduced.
Neither wrapper is treated as an independent or constant native callback.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Witgen Zcash.Circuits

/-- The running-sum wrapper retains every read in the original mapped builder. -/
theorem mulComplete_zWit_support (z : AssignedCell Fp)
    (ebits : MOver Fp (AssignedCell Fp) (ℕ → BExpr Fp)) (iter : ℕ) :
    WitnessFunctionSupport
      (valueBuilderReads (value := field)
        ((fun bs => Ecc.MulComplete.zWitExpr (.expr z) bs iter) <$> ebits))
      (fun env => ((Ecc.MulComplete.zWit z ebits iter).eval env)[0]) := by
  intro left right agreement
  simp only [Ecc.MulComplete.zWit, MOver.eval_toIRScalar]
  exact valueBuilderReads_eval (value := field) _ left right agreement

/-- The signed-coordinate wrapper retains both its selected bit and coordinate reads. -/
theorem mulComplete_yPWit_support (y : AssignedCell Fp)
    (ebits : MOver Fp (AssignedCell Fp) (ℕ → BExpr Fp)) (iter : ℕ) :
    WitnessFunctionSupport
      (valueBuilderReads (value := field)
        ((fun bs => .ite (bs iter) (.expr y) (FExprOver.neg (.expr y))) <$> ebits))
      (fun env => ((Ecc.MulComplete.yPWit y ebits iter).eval env)[0]) := by
  intro left right agreement
  simp only [Ecc.MulComplete.yPWit, MOver.eval_toIRScalar]
  exact valueBuilderReads_eval (value := field) _ left right agreement

end Zcash.Snark.ZeroKnowledge
