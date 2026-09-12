import Zcash.Snark.ZeroKnowledge.NativeCopyLoops
import Zcash.Circuits.Ecc.MulComplete

/-!
# Native-source obligations around incomplete multiplication

Complete addition and complete multiplication use structured witness IR. These
source proofs therefore discharge every native-copy obligation for those gadgets,
including accumulator-dependent loops of arbitrary length.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2
open Zcash.Circuits.Ecc

set_option maxRecDepth 8192

/-- The original complete addition gadget contains no native advice programs. -/
theorem add_nativeCopiesSound (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (region : RegionIndex) (cfg : Add.Config) (offset : ℕ) (input : Var Add.Inputs Fp) :
    RegionNativeCopiesSound place source region
      (((Zcash.Circuits.Ecc.Add.add).call cfg offset input).operations region) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Zcash.Circuits.Ecc.Add.add, circuit_norm,
    regionNativeCopiesSound_cons, regionNativeCopiesSound_nil,
    Witgen.WitgenIROver.ofFExpr, NativeCopyOperationSound, true_and]

/-- Every advice program in a complete multiplication round is structured IR. -/
theorem mulComplete_round_nativeCopiesSound (place : RegionIndex → ℕ)
    (source : NativeAdviceCopySource) (region : RegionIndex) (cfg : MulComplete.Config)
    (offset bit iter : ℕ) (input : Var MulComplete.RoundInputs Fp) :
    RegionNativeCopiesSound place source region
      (((MulComplete.round bit iter).call cfg offset input).operations region) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [MulComplete.round, MulComplete.roundSynthesize, circuit_norm,
    regionNativeCopiesSound_append, regionNativeCopiesSound_cons,
    MulComplete.zWit, MulComplete.yPWit, Witgen.WitgenIROver.ofFExpr,
    NativeCopyOperationSound, true_and]
  exact ⟨add_nativeCopiesSound place source region cfg.addConfig offset _,
    add_nativeCopiesSound place source region cfg.addConfig (offset + 1) _⟩

/-- All complete multiplication rounds and their initial copies contain no native advice programs. -/
theorem mulComplete_assign_nativeCopiesSound (place : RegionIndex → ℕ)
    (source : NativeAdviceCopySource) (region : RegionIndex) (cfg : MulComplete.Config)
    (offset count bit : ℕ) (input : Var MulComplete.Inputs Fp) :
    RegionNativeCopiesSound place source region
      (((MulComplete.assign_region count bit).call cfg offset input).operations region) := by
  rw [FormalRegionCircuit.call_operations]
  change RegionNativeCopiesSound place source region
    ((MulComplete.assignRegionSynthesize count bit cfg offset input).operations region)
  rw [MulComplete.assignRegionSynthesize_operations]
  simp only [MulComplete.startCopy, circuit_norm, regionNativeCopiesSound_cons,
    Witgen.WitgenIROver.ofFExpr, NativeCopyOperationSound, true_and]
  apply regionNativeCopiesSound_foldRange
  intro index current accumulator
  simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure, List.append_nil]
  exact mulComplete_round_nativeCopiesSound place source region cfg current bit index _

end Zcash.Snark.ZeroKnowledge
