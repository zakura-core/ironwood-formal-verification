import Zcash.Snark.ZeroKnowledge.ActionGateSourceCertificate
import Zcash.Snark.ZeroKnowledge.GateIndexedCoverage
import Zcash.Meta.ActivationCoverage

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option stderrAsMessages false
set_option trace.Zcash.activationCoverage true

/-- Every configured gate has its original source entry at every active row. -/
theorem actionCircuit_gateActivationCoverage_certificate :
    gateActivationCoverageCheck (actionCircuit.constraintSystem.gates.map sourceGateLabel)
      actionCircuit.selectorActivations actionGateActivationSourceCertificate.entries = true := by
  have normalizeCheck (labels : List (ℕ × String × ℕ)) :
      gateActivationCoverageCheck (actionCircuit.constraintSystem.gates.map sourceGateLabel)
        actionCircuit.selectorActivations labels =
      gateActivationCoverageCheck (Internal.actionCircuitImpl.constraintSystem.gates.map sourceGateLabel)
        (placeSelectorTrace actionRegionStartsCertificate (actionSourceSelectorTrace actionConfig)) labels := by
    rw [actionCircuit_selectorActivations_eq_sourceTrace, actionCircuit_regionStarts_eq_certificate,
      Internal.actionCircuit_eq_impl]
  rw [normalizeCheck]
  change gateActivationCoverageCheck (Internal.actionCircuitImpl.constraintSystem.gates.map sourceGateLabel)
    (placeSelectorTrace actionRegionStartsCertificate (actionSourceSelectorTrace actionConfig))
    actionGateActivationSourceCertificate.entries = true
  rw [← gateActivationCoverageScan_eq]
  rw [← gateIndexedCoverageScan_original]
  check_activation_coverage

/-- The gate coverage result is indexed by the original complete Action operations. -/
theorem actionCircuit_gateActivationCoverage :
    gateActivationCoverageCheck (actionCircuit.constraintSystem.gates.map sourceGateLabel)
      actionCircuit.selectorActivations
      (sourceGateActivationLabels actionCircuit.placement actionCircuit.operations 0) = true := by
  rw [← actionGateActivationSourceCertificate.source_eq]
  exact actionCircuit_gateActivationCoverage_certificate

end Zcash.Snark.ZeroKnowledge
