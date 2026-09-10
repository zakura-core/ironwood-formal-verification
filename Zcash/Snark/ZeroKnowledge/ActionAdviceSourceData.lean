import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceChunks.Chunk032

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
set_option stderrAsMessages false
set_option linter.constructorNameAsVariable false
set_option trace.Zcash.adviceSourceCertificate true

/-- Original instruction annotations, reflected and checked by the kernel. -/
noncomputable def actionAdviceSourceCertificateRaw : AdviceSourceCertificate actionAdviceSourcePrograms :=
  actionAdviceSourceChunk032.finish AdviceSourceCertificate.nil

/-- The normalized data indexed by the actual Action program. -/
noncomputable def actionAdviceSourceCertificate : AdviceSourceCertificate actionAdviceAliasPrograms :=
  AdviceSourceCertificate.transport actionAdviceSourcePrograms_eq actionAdviceSourceCertificateRaw

end Zcash.Snark.ZeroKnowledge
