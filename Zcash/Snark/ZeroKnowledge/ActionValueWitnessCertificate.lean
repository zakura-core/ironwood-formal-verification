import Zcash.Meta.AdviceSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionAdviceAliasPlan

/-!
# Read certificates for the original value-commitment stage

The certificate follows the actual short multiplication, full-width blinding
multiplication, and complete addition at source region 266. It retains all 1,083
original instructions and their copy tags, for arbitrary original stage inputs.
It is a kernel-evaluated proof artifact; read availability and the global alias
scan still belong to the complete Action certificate.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000

/-- Semantic read annotations for every original value-commitment instruction. -/
noncomputable def actionValueSourceCertificate (input : Var ValueCommit.Inputs Fp) :
    AdviceSourceCertificate (F := Fp)
      (circuitAdviceAliases (F := Fp)
        (fun region => actionRegionStartsCertificate.getD region 0)
        (actionNativeAdviceCopySource (fun region => actionRegionStartsCertificate.getD region 0))
        (((ValueCommit.circuit orchardBases.valueCommitV orchardBases.valueCommitR).call
          (actionConfig.eccConfig.mulFixedShort, actionConfig.eccConfig.mulFixedFull,
            actionConfig.eccConfig.add) input).operations 266) 266) := by
  certify_source_advice

/-- Every input gives the same complete 1,083-instruction source certificate. -/
theorem actionValueSource_annotationCount (input : Var ValueCommit.Inputs Fp) :
    (actionValueSourceCertificate input).annotations.length = 1083 := by
  kernel_rfl

end Zcash.Snark.ZeroKnowledge
