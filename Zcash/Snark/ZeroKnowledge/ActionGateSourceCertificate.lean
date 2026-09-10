import Zcash.Meta.SourceListCertificate
import Zcash.Snark.ZeroKnowledge.DirectGateLabels
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace

/-!# Gate activations from the original Action source

The certificate retains the configured gate name, selector index, and placed row
of every original activation. Source equations and the proved V1 placement link
the finite metadata directly to the actual Action circuit.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option stderrAsMessages false
set_option trace.Zcash.sourceListCertificate true

/-- Original Action activations at the source-certified placement. -/
def actionGateSourceLabels : List (ℕ × String × ℕ) :=
  operationSourceGateLabels (fun region => actionRegionStartsCertificate.getD region 0)
    ((Circuit.mainPost Specs.Sinsemilla.orchardGenerators orchardBases actionConfig ()).operations 0) 0

/-- The finite source expression is exactly the actual compiler's gate schedule. -/
theorem actionGateSourceLabels_eq :
    actionGateSourceLabels =
      sourceGateActivationLabels actionCircuit.placement actionCircuit.operations 0 := by
  change actionGateSourceLabels = sourceGateActivationLabels
    (fun region => actionCircuit.regionStarts.getD region 0) actionCircuit.operations 0
  rw [actionCircuit_regionStarts_eq_certificate, Internal.actionCircuit_eq_impl]
  unfold actionGateSourceLabels
  rw [operationSourceGateLabels_eq]
  rfl

/-- Kernel-checked reflection of every original Action gate activation. -/
noncomputable def actionGateSourceCertificateRaw : SourceListCertificate actionGateSourceLabels := by
  unfold actionGateSourceLabels
  certify_source_list

/-- The same normalized metadata with the actual circuit as its source. -/
noncomputable def actionGateActivationSourceCertificate :
    SourceListCertificate
      (sourceGateActivationLabels actionCircuit.placement actionCircuit.operations 0) :=
  SourceListCertificate.transport actionGateSourceLabels_eq actionGateSourceCertificateRaw

/-- Gate names disambiguate the configured gates sharing selector 18. -/
theorem actionCircuit_gateLabels_nodup :
    (actionCircuit.constraintSystem.gates.map sourceGateLabel).Nodup := by
  rw [Internal.actionCircuit_eq_impl]
  decide +kernel

end Zcash.Snark.ZeroKnowledge
