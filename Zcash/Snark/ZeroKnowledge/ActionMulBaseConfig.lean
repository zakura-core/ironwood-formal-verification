import Zcash.Snark.ZeroKnowledge.NativeBaseCopySupport
import Zcash.Circuits.Action.TopLevel

/-!
# Shared-base columns in the actual Action configuration

The kernel reduces the original closed configure program to check the two base
column indices and their separation from every accumulator and slope column.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits.Action

set_option maxRecDepth 8192

/-- The high half uses the shared base columns and separate auxiliary columns. -/
theorem actionMul_hiBaseConfig :
    MulIncompleteBaseSeparated actionConfig.eccConfig.mul.hiConfig ∧
    actionConfig.eccConfig.mul.hiConfig.xP.index = 0 ∧
    actionConfig.eccConfig.mul.hiConfig.yP.index = 1 := by
  simp only [MulIncompleteBaseSeparated, List.forall_mem_cons]
  decide +kernel

/-- The low half uses the same base columns and separate auxiliary columns. -/
theorem actionMul_loBaseConfig :
    MulIncompleteBaseSeparated actionConfig.eccConfig.mul.loConfig ∧
    actionConfig.eccConfig.mul.loConfig.xP.index = 0 ∧
    actionConfig.eccConfig.mul.loConfig.yP.index = 1 := by
  simp only [MulIncompleteBaseSeparated, List.forall_mem_cons]
  decide +kernel

end Zcash.Snark.ZeroKnowledge
