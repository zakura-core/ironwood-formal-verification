import Zcash.Snark.ZeroKnowledge.ActionLookupCoverageTree

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000

/-- Every configured lookup has its original source entry at every active master row. -/
theorem actionCircuit_lookupActivationCoverage_certificate :
    lookupActivationCoverageCheck
      (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
      actionCircuit.selectorActivations actionLookupActivationSourceCertificate.entries = true := by
  have normalizeCheck (labels : List (ℕ × ℕ)) :
      lookupActivationCoverageCheck
        (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
        actionCircuit.selectorActivations labels =
      lookupActivationCoverageCheck
        (Internal.actionCircuitImpl.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
        (placeSelectorTrace actionRegionStartsCertificate (actionSourceSelectorTrace actionConfig)) labels := by
    rw [actionCircuit_selectorActivations_eq_sourceTrace, actionCircuit_regionStarts_eq_certificate,
      Internal.actionCircuit_eq_impl]
  rw [normalizeCheck]
  change lookupActivationCoverageCheck
    (Internal.actionCircuitImpl.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
    (placeSelectorTrace actionRegionStartsCertificate (actionSourceSelectorTrace actionConfig))
    actionLookupActivationSourceCertificate.entries = true
  rw [← lookupActivationCoverageScan_eq]
  rw [← actionLookupCoverageMasters.source_eq, ← actionCoverageActivations.source_eq,
    ← actionLookupCoverageLabels.source_eq]
  exact actionLookupCoverage_check

/-- The lookup coverage result is indexed by the original complete Action operations. -/
theorem actionCircuit_lookupActivationCoverage :
    lookupActivationCoverageCheck
      (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
      actionCircuit.selectorActivations
      (sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0) = true := by
  rw [← actionLookupActivationSourceCertificate.source_eq]
  exact actionCircuit_lookupActivationCoverage_certificate

end Zcash.Snark.ZeroKnowledge
