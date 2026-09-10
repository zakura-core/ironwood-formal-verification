import Zcash.Snark.ZeroKnowledge.ActionGateSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionCoverageData

/-!
# Exact indexed gate metadata for Action coverage

The configured registry is normalized before its indices are used in the source
labels. Every normalization retains an equality to the original metadata.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000

/-- The complete configured selector/name registry used by the original gate check. -/
noncomputable def actionGateCoverageRegistry : SourceListCertificate
    (Internal.actionCircuitImpl.constraintSystem.gates.map sourceGateLabel) := by
  certify_coverage_data

/-- Configured selector/index pairs use the exact stored gate registry. -/
noncomputable def actionGateCoverageEntries : SourceListCertificate
    (actionGateCoverageRegistry.entries.map
      (fun gate => (gate.1, actionGateCoverageRegistry.entries.idxOf gate))) := by
  certify_coverage_data

/-- Every original source name and row is indexed against the same configured registry. -/
noncomputable def actionGateCoverageLabels : SourceListCertificate
    (actionGateActivationSourceCertificate.entries.map
      (gateCoverageIndexLabel actionGateCoverageRegistry.entries)) := by
  certify_coverage_data

end Zcash.Snark.ZeroKnowledge
