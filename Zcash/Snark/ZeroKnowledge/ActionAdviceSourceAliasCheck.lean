import Zcash.Snark.ZeroKnowledge.ActionAdviceAliasChunks.Chunk019
import Zcash.Meta.KernelRfl

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000

/-- The final scan continuation leaves no original source entries unchecked. -/
private theorem scan_remainder_empty : actionAdviceAliasChunk019.remainingEntries = [] := by
  kernel_rfl

/-- Every repeated advice write preserves the source-certified alias relation. -/
theorem actionAdviceSource_aliasPlan :
    adviceAliasMapPlan ∅ (adviceAliasAddressData
      (actionAdviceSourceCertificate.annotations.map (fun entry => (entry.1.instruction, entry.2)))) = true := by
  rw [adviceAliasMapPlan_eq_scan]
  apply actionAdviceAliasChunk019.finish
  simp only [scan_remainder_empty, adviceMapScan]

end Zcash.Snark.ZeroKnowledge
