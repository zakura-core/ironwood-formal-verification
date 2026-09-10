import Zcash.Snark.ZeroKnowledge.ActionAdviceReadChunks.Chunk019
import Zcash.Meta.KernelRfl

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000

/-- The final scan continuation leaves no original source entries unchecked. -/
private theorem scan_remainder_empty : actionAdviceReadChunk019.remainingEntries = [] := by
  kernel_rfl

/-- Every advice read is available when the original program executes. -/
theorem actionAdviceSource_readPlan :
    adviceSupportMapPlan actionCircuit.placement ∅
      actionAdviceSourceCertificate.readCertificate.annotations = true := by
  change adviceSupportMapPlan (fun region => actionCircuit.regionStarts.getD region 0) ∅
    actionAdviceSourceCertificate.readCertificate.annotations = true
  rw [actionCircuit_regionStarts_eq_certificate]
  rw [adviceSupportMapPlan_eq_scan]
  apply actionAdviceReadChunk019.finish
  simp only [scan_remainder_empty, adviceMapScan]

end Zcash.Snark.ZeroKnowledge
