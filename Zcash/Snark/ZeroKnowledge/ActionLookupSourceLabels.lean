import Zcash.Meta.SourceListCertificate
import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace

/-!
# Original Action lookup-source labels

Gate activations can share lookup master selectors. The source projection retains the
original enableLookup operations and their exact placed rows, so the subsequent
coverage check does not infer lookup membership from a selector index alone.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 50000

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

end Zcash.Snark.ZeroKnowledge
