import Zcash.Snark.ZeroKnowledge.NativeMulCopySupport
import Zcash.Snark.ZeroKnowledge.ActionMulBaseConfig
import Zcash.Snark.ZeroKnowledge.ActionBaseCopySources

/-!
# Native copy sources for the actual Action multiplier

The original complete multiplication region uses the checked Action column
configuration. Its native annotations have exact base-copy semantics for every
input and environment, without field-value or scalar-bit exclusions.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits.Action
open Zcash.Circuits.Ecc

/-- The original Action multiplication region satisfies every native copy-source obligation. -/
theorem actionMul_nativeCopiesSound (place : RegionIndex → ℕ) (region : RegionIndex)
    (input : Var Mul.Inputs Fp) :
    RegionNativeCopiesSound place (actionNativeAdviceCopySource place) region
      ((Mul.mainSynthesize actionConfig.eccConfig.mul input).operations region) := by
  apply mul_main_nativeCopiesSound place (actionNativeAdviceCopySource place) region
    actionConfig.eccConfig.mul input
  · exact actionNativeAdviceCopySource_previous place region _ _
      actionMul_hiBaseConfig.2.1 actionMul_hiBaseConfig.2.2
  · exact actionNativeAdviceCopySource_previous place region _ _
      actionMul_loBaseConfig.2.1 actionMul_loBaseConfig.2.2
  · exact actionMul_hiBaseConfig.1
  · exact actionMul_loBaseConfig.1

end Zcash.Snark.ZeroKnowledge
