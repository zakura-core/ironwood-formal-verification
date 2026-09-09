import Zcash.Meta.SourceListCertificate
import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace

/-!
# Lookup activations from the original Action source

Gate activations can share lookup master selectors. This certificate retains the
original enableLookup operations and their exact placed rows, so the subsequent
coverage check does not infer lookup membership from a selector index alone.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Zcash.sourceCertificate.chunkSteps 64
set_option stderrAsMessages false
set_option trace.Zcash.sourceListCertificate true

/-- Original lookup activations at the source-certified Action placement. -/
def actionLookupSourceLabels : List (ℕ × ℕ) :=
  operationSourceLookupLabels (fun region => actionRegionStartsCertificate.getD region 0)
    ((Circuit.mainPost Specs.Sinsemilla.orchardGenerators orchardBases actionConfig ()).operations 0) 0

/-- The normalized source expression retains the actual complete lookup schedule. -/
theorem actionLookupSourceLabels_eq :
    actionLookupSourceLabels = sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0 := by
  change actionLookupSourceLabels = sourceLookupActivationLabels
    (fun region => actionCircuit.regionStarts.getD region 0) actionCircuit.operations 0
  rw [actionCircuit_regionStarts_eq_certificate, Internal.actionCircuit_eq_impl]
  unfold actionLookupSourceLabels
  rw [operationSourceLookupLabels_eq]
  rfl

/-- Kernel-checked reflection of all original Action lookup activations. -/
noncomputable def actionLookupSourceCertificateRaw : SourceListCertificate actionLookupSourceLabels := by
  unfold actionLookupSourceLabels
  certify_source_list

/-- The same normalized metadata explicitly indexed by the actual Action circuit. -/
noncomputable def actionLookupActivationSourceCertificate :
    SourceListCertificate (sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0) :=
  SourceListCertificate.transport actionLookupSourceLabels_eq actionLookupSourceCertificateRaw

/-- The configured Action lookup arguments have distinct master selectors. -/
theorem actionCircuit_lookupMasters_nodup :
    (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index)).Nodup := by
  rw [Internal.actionCircuit_eq_impl]
  decide +kernel

end Zcash.Snark.ZeroKnowledge
