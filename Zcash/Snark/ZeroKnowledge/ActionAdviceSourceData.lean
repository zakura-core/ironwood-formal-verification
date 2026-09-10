import Zcash.Meta.AdviceSourceCertificate
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionNativeRouting
import Zcash.Snark.ZeroKnowledge.ActionWitnessRows

/-!
# Complete original Action witness certificate

The certificate follows the original source at the proved V1 placement, retaining
all instructions and semantic read annotations. Kernel evaluation of the global
read and alias scans supplies the existing witness-execution theorem for arbitrary
public inputs and application hints. Semantic witness validity is not assumed by
this execution theorem.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option stderrAsMessages false
set_option linter.constructorNameAsVariable false
set_option trace.Zcash.adviceSourceCertificate true

/-- The exact original Action source at its certified placement. -/
def actionAdviceSourcePrograms : List (PlacedAdviceProgram Fp × Option AdviceAddress) :=
  circuitAdviceAliases (F := Fp)
    (fun region => actionRegionStartsCertificate.getD region 0)
    (actionNativeAdviceCopySource (fun region => actionRegionStartsCertificate.getD region 0))
    ((Circuit.mainPost Specs.Sinsemilla.orchardGenerators orchardBases actionConfig ()).operations 0) 0

/-- Source reflection retains the actual compiler instructions and copy tags. -/
theorem actionAdviceSourcePrograms_eq : actionAdviceSourcePrograms = actionAdviceAliasPrograms := by
  unfold actionAdviceAliasPrograms
  rw [actionCircuit_regionStarts_eq_certificate, Internal.actionCircuit_eq_impl]
  rfl

/-- Original instruction annotations, reflected and checked by the kernel. -/
noncomputable def actionAdviceSourceCertificateRaw : AdviceSourceCertificate actionAdviceSourcePrograms := by
  unfold actionAdviceSourcePrograms
  certify_source_advice

/-- The normalized data indexed by the actual Action program. -/
noncomputable def actionAdviceSourceCertificate : AdviceSourceCertificate actionAdviceAliasPrograms :=
  AdviceSourceCertificate.transport actionAdviceSourcePrograms_eq actionAdviceSourceCertificateRaw

end Zcash.Snark.ZeroKnowledge
