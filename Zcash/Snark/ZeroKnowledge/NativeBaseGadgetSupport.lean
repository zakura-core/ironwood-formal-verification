import Zcash.Snark.ZeroKnowledge.NativeBaseLoopSupport
import Zcash.Snark.ZeroKnowledge.NativeCopyComposition

/-!
# Native copy certificates for incomplete multiplication gadgets

The initialization and finalization callbacks write only non-base columns. The
interior uses the checked loop certificate, covering the original operations for
any loop length without treating every native callback as a copy.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2
open Zcash.Circuits.Ecc

set_option maxRecDepth 8192

/-- All annotated native writes in the original gadget are the certified interior base copies. -/
theorem mulIncomplete_doubleAndAdd_nativeCopiesSound
    (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (region : RegionIndex) (cfg : MulIncomplete.Config) (offset count bit : ℕ)
    (input : Var MulIncomplete.Inputs Fp)
    (hsource : PreviousBaseCopySources place source region cfg.xP cfg.yP)
    (hseparated : MulIncompleteBaseSeparated cfg) :
    RegionNativeCopiesSound place source region
      (((MulIncomplete.double_and_add count bit).call cfg offset input).operations region) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [MulIncomplete.double_and_add, circuit_norm,
    regionNativeCopiesSound_append, regionNativeCopiesSound_cons,
    regionNativeCopiesSound_nil, Witgen.WitgenIROver.ofFExpr,
    MulIncomplete.initLambdaWit, MulIncomplete.stepWit, MulIncomplete.readWit,
    NativeCopyOperationSound, true_and, and_true]
  refine ⟨?_, ?_, mulIncomplete_loop_nativeCopiesSound place source region cfg offset count bit
    input.alpha hsource hseparated, ?_, ?_, ?_⟩ <;>
    intro address haddress
  all_goals exact False.elim (previousBaseCopySources_nonbase place source region cfg
    hsource hseparated _ (by simp) _ _ haddress)

end Zcash.Snark.ZeroKnowledge
