import Zcash.Snark.ZeroKnowledge.ActionLookupSourceChunks.Chunk081
import Zcash.Meta.KernelRfl

/-!
# Lookup activations from the original Action source

Gate activations can share lookup master selectors. This certificate retains the
original enableLookup operations and their exact placed rows, so the subsequent
coverage check does not infer lookup membership from a selector index alone.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 50000

/-- The complete lookup continuation leaves no source operations unchecked. -/
private theorem lookup_remainder_empty : actionLookupSourceChunk081.remaining = [] := by
  kernel_rfl

/-- Kernel-checked reflection of all original Action lookup activations. -/
noncomputable def actionLookupSourceCertificateRaw : SourceListCertificate actionLookupSourceLabels :=
  actionLookupSourceChunk081.finish <|
    SourceListCertificate.transport lookup_remainder_empty.symm SourceListCertificate.nil

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
