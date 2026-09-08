import Zcash.Snark.ZeroKnowledge.NativeCopyRegions
import Clean.Halo2.Subcircuit

/-!
# Lifting native copy certificates through region calls

The original region-to-circuit adapter preserves the native-copy predicate and
uses the same source operations at the same region index.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- Promoting the original region circuit preserves its exact native-copy obligation. -/
theorem circuitNativeCopiesSound_toFormal {F ConfigInput Config : Type} [FiniteField F]
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (child : FormalRegionCircuit F ConfigInput Config Input Output) (name : String)
    (cfg : Config) (input : Var Input F) (region : RegionIndex) :
    CircuitNativeCopiesSound place source (((child.toFormal name).call cfg input).operations region) region ↔
      RegionNativeCopiesSound place source region ((child.call cfg 0 input).operations region) := by
  rw [FormalCircuit.call_operations, FormalRegionCircuit.call_operations]
  change (_ ∧ True) ↔ _
  exact ⟨And.left, fun h => ⟨h, trivial⟩⟩

end Zcash.Snark.ZeroKnowledge
