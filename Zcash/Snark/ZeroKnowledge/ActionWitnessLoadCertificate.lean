import Zcash.Meta.AdviceSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionAdviceAliasPlan

/-!
# The original Action witness-loading stage

This certificate covers the exact first eight source regions, using the proved
Action placement and original copy-source function. All eleven instructions
retain their source programs and copy tags. Both finite scans are checked by the
kernel. The later Action stages and final witness extension remain separate.

The certificate is a proof artifact evaluated by the kernel. Code generation is
disabled for its expanded source data, which can contain kernel-only auxiliary
definitions from the original circuit combinators. This declaration is not part
of the executable witness constructor.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 50000

/-- Certified reads for every original instruction in the initial witness-loading stage. -/
noncomputable def actionWitnessLoadSourceCertificate : AdviceSourceCertificate (F := Fp)
    (circuitAdviceAliases (F := Fp)
      (fun region => actionRegionStartsCertificate.getD region 0)
      (actionNativeAdviceCopySource (fun region => actionRegionStartsCertificate.getD region 0))
      ((Circuit.synthWitness Specs.Sinsemilla.orchardGenerators Circuit.hintWitnesses
        actionConfig).operations 0) 0) := by
  certify_source_advice

/-- Every original loading-stage read is available when it is used. -/
theorem actionWitnessLoad_readPlan :
    adviceSupportMapPlan (fun region => actionRegionStartsCertificate.getD region 0)
      ∅ actionWitnessLoadSourceCertificate.readCertificate.annotations = true := by
  kernel_rfl

/-- Every original loading-stage write and copy satisfies the finite alias policy. -/
theorem actionWitnessLoad_aliasPlan :
    adviceAliasMapPlan ∅ (adviceAliasAddressData
      (actionWitnessLoadSourceCertificate.annotations.map
        (fun entry => (entry.1.instruction, entry.2)))) = true := by
  kernel_rfl

/-- The checked certificate contains exactly the eleven original loading-stage instructions. -/
theorem actionWitnessLoad_annotationCount :
    actionWitnessLoadSourceCertificate.annotations.length = 11 := by
  kernel_rfl

end Zcash.Snark.ZeroKnowledge
