import Zcash.Snark.ZeroKnowledge.ActionLookupSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionCoverageData

/-!
# Exact lookup metadata for Action coverage

The configured masters and original source labels are normalized with exact
source equalities. The lookup and gate checks share the same activation data.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000

/-- The complete configured lookup registry retains each original master selector. -/
noncomputable def actionLookupCoverageMasters : SourceListCertificate
    (Internal.actionCircuitImpl.constraintSystem.lookups.map
      (fun lookup => lookup.masterSelector.index)) := by
  certify_coverage_data

/-- The original source-certified master and row pairs are retained in full. -/
noncomputable def actionLookupCoverageLabels : SourceListCertificate
    actionLookupActivationSourceCertificate.entries := by
  certify_coverage_data

end Zcash.Snark.ZeroKnowledge
