import Zcash.Snark.ZeroKnowledge.NativeBaseGadgetSupport
import Zcash.Snark.ZeroKnowledge.NativeArithmeticCopySupport
import Zcash.Circuits.Ecc.Mul

/-!
# Native copy certificates for complete variable-base multiplication

The proof composes the original initialization, both incomplete halves, the
complete phase, and final addition. Only the two incomplete halves contain
native base-copy callbacks, and each uses its own checked column separation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2
open Zcash.Circuits.Ecc

set_option maxRecDepth 8192

/-- Every annotated native write in the original full multiplication region is a base copy. -/
theorem mul_main_nativeCopiesSound (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (region : RegionIndex) (cfg : Mul.Config) (input : Var Mul.Inputs Fp)
    (hsourceHi : PreviousBaseCopySources place source region cfg.hiConfig.xP cfg.hiConfig.yP)
    (hsourceLo : PreviousBaseCopySources place source region cfg.loConfig.xP cfg.loConfig.yP)
    (hseparatedHi : MulIncompleteBaseSeparated cfg.hiConfig)
    (hseparatedLo : MulIncompleteBaseSeparated cfg.loConfig) :
    RegionNativeCopiesSound place source region ((Mul.mainSynthesize cfg input).operations region) := by
  simp only [Mul.mainSynthesize, circuit_norm, regionNativeCopiesSound_append,
    regionNativeCopiesSound_cons, Witgen.WitgenIROver.ofFExpr,
    NativeCopyOperationSound, true_and]
  exact ⟨add_nativeCopiesSound place source region cfg.addConfig Mul.offInit _,
    mulIncomplete_doubleAndAdd_nativeCopiesSound place source region cfg.hiConfig Mul.offHi 124 0
      _ hsourceHi hseparatedHi,
    mulIncomplete_doubleAndAdd_nativeCopiesSound place source region cfg.loConfig Mul.offLo 125 125
      _ hsourceLo hseparatedLo,
    mulComplete_assign_nativeCopiesSound place source region cfg.completeConfig Mul.offComp 3 251 _,
    add_nativeCopiesSound place source region cfg.addConfig Mul.offLsb _⟩

end Zcash.Snark.ZeroKnowledge
