import Zcash.Snark.ZeroKnowledge.ActionGateSourceChunks.Chunk021

/-!# Gate activations from the original Action source

The certificate retains the configured gate name, selector index, and placed row
of every original activation. Source equations and the proved V1 placement link
the finite metadata directly to the actual Action circuit.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 50000
set_option stderrAsMessages false
set_option trace.Zcash.sourceListCertificate true

/-- Kernel-checked reflection of every original Action gate activation. -/
noncomputable def actionGateSourceCertificateRaw : SourceListCertificate actionGateSourceLabels :=
  actionGateSourceChunk021.finish SourceListCertificate.nil

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
