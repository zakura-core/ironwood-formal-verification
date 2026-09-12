import Zcash.Snark.ZeroKnowledge.NativeBaseCopySupport
import Zcash.Circuits.Ecc.MulIncomplete

/-!
# Native copy semantics throughout incomplete multiplication loops

The proof follows the original loop operations and applies the round certificate
at each source index. It is independent of the bit count and scalar values.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2
open Zcash.Circuits.Ecc

/-- Every original native base write in an arbitrary-length incomplete loop has the preceding-row source. -/
theorem mulIncomplete_loop_nativeCopiesSound (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (region : RegionIndex) (cfg : MulIncomplete.Config) (offset count bit : ℕ)
    (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (hsource : PreviousBaseCopySources place source region cfg.xP cfg.yP)
    (hseparated : MulIncompleteBaseSeparated cfg) :
    RegionNativeCopiesSound place source region
      (((MulIncomplete.loop count bit).call cfg offset alpha).operations region) := by
  intro column row callback hmem address haddress
  rw [FormalRegionCircuit.call_operations] at hmem
  change RegionOperation.assignAdvice column row (.native callback) ∈
    (MulIncomplete.loopProgram count bit cfg offset alpha).operations region at hmem
  rw [MulIncomplete.loopProgram_operations, RegionCircuit.forRange'_operations] at hmem
  obtain ⟨body, hbody, hmem⟩ := List.mem_flatten.mp hmem
  obtain ⟨index, hbody⟩ := List.mem_ofFn.mp hbody
  subst body
  simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil, Nat.mul_one] at hmem
  exact mulIncomplete_round_nativeCopiesSound place source region cfg (offset + index.val) (bit + index.val)
    alpha hsource hseparated column row callback hmem address haddress

end Zcash.Snark.ZeroKnowledge
