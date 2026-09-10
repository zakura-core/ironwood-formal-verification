import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace
import Zcash.Meta.ActivationCoverage

/-!
# Exact selector-activation data for Action coverage

The gate and lookup checks use the same source trace and certified placement.
This static certificate normalizes that metadata once for both checks.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000

/-- Shared activation metadata retains every source selector and its placed row. -/
noncomputable def actionCoverageActivations : SourceListCertificate
    (placeSelectorTrace actionRegionStartsCertificate (actionSourceSelectorTrace actionConfig)) := by
  certify_coverage_data

end Zcash.Snark.ZeroKnowledge
