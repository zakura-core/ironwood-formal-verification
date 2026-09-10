import Zcash.Meta.SourceListCertificate
import Zcash.Snark.ZeroKnowledge.DirectGateLabels
import Zcash.Snark.ZeroKnowledge.ActionOrderedStarts
import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace

/-!# Initial gate-source certificate continuation

The prefix retains original gate names, selector indices, and placed rows. Its
continuation requires a certificate for the exact unprocessed source, allowing
the complete gate schedule to be assembled from bounded declarations.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 50000
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

private noncomputable def gateSourcePiece0000 :
    SourceCertificatePiece SourceListCertificate (actionGateSourceLabels) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0001 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0000.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0002 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0001.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0003 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0002.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0004 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0003.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0005 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0004.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0006 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0005.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0007 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0006.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0008 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0007.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0009 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0008.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0010 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0009.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0011 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0010.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0012 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0011.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0013 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0012.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0014 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0013.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0015 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0014.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0016 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0015.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0017 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0016.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0018 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0017.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0019 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0018.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0020 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0019.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0021 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0020.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0022 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0021.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0023 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0022.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0024 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0023.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0025 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0024.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0026 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0025.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0027 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0026.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0028 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0027.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0029 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0028.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0030 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0029.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0031 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0030.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0032 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0031.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0033 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0032.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0034 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0033.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0035 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0034.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0036 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0035.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0037 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0036.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0038 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0037.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0039 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0038.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0040 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0039.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0041 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0040.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0042 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0041.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0043 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0042.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0044 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0043.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0045 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0044.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0046 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0045.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0047 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0046.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0048 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0047.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0049 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0048.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0050 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0049.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0051 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0050.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0052 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0051.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0053 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0052.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0054 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0053.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0055 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0054.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0056 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0055.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0057 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0056.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0058 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0057.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0059 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0058.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0060 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0059.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0061 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0060.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0062 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0061.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0063 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0062.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0064 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0063.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0065 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0064.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0066 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0065.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0067 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0066.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0068 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0067.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0069 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0068.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0070 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0069.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0071 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0070.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0072 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0071.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0073 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0072.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0074 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0073.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0075 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0074.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0076 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0075.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0077 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0076.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0078 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0077.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0079 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0078.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0080 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0079.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0081 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0080.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0082 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0081.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0083 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0082.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0084 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0083.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0085 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0084.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0086 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0085.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0087 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0086.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0088 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0087.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0089 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0088.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0090 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0089.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0091 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0090.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0092 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0091.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0093 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0092.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0094 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0093.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0095 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0094.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0096 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0095.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0097 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0096.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0098 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0097.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0099 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0098.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0100 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0099.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0101 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0100.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0102 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0101.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0103 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0102.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0104 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0103.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0105 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0104.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0106 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0105.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0107 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0106.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0108 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0107.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0109 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0108.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0110 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0109.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0111 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0110.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0112 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0111.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0113 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0112.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0114 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0113.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0115 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0114.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0116 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0115.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0117 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0116.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0118 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0117.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0119 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0118.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0120 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0119.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0121 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0120.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0122 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0121.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0123 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0122.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0124 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0123.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0125 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0124.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0126 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0125.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0127 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0126.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0128 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0127.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0129 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0128.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0130 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0129.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0131 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0130.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0132 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0131.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0133 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0132.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0134 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0133.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0135 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0134.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0136 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0135.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0137 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0136.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0138 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0137.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0139 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0138.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0140 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0139.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0141 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0140.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0142 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0141.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0143 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0142.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0144 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0143.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0145 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0144.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0146 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0145.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0147 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0146.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0148 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0147.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0149 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0148.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0150 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0149.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0151 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0150.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0152 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0151.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0153 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0152.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0154 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0153.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0155 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0154.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0156 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0155.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0157 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0156.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0158 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0157.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0159 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0158.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0160 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0159.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0161 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0160.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0162 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0161.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0163 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0162.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0164 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0163.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0165 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0164.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0166 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0165.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0167 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0166.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0168 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0167.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0169 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0168.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0170 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0169.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0171 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0170.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0172 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0171.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0173 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0172.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0174 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0173.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0175 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0174.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0176 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0175.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0177 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0176.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0178 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0177.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0179 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0178.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0180 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0179.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0181 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0180.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0182 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0181.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0183 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0182.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0184 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0183.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0185 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0184.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0186 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0185.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0187 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0186.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0188 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0187.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0189 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0188.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0190 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0189.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0191 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0190.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0192 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0191.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0193 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0192.remaining) := by
  certify_source_list_piece 256 64

private noncomputable def gateSourcePiece0194 :
    SourceCertificatePiece SourceListCertificate (gateSourcePiece0193.remaining) := by
  certify_source_list_piece 256 64

/-- A checked prefix of the gate schedule, retaining the remaining original source. -/
noncomputable def actionGateSourcePrefix :
    SourceCertificatePiece SourceListCertificate actionGateSourceLabels where
  remaining := gateSourcePiece0194.remaining
  finish suffix :=
    gateSourcePiece0000.finish <|
    gateSourcePiece0001.finish <|
    gateSourcePiece0002.finish <|
    gateSourcePiece0003.finish <|
    gateSourcePiece0004.finish <|
    gateSourcePiece0005.finish <|
    gateSourcePiece0006.finish <|
    gateSourcePiece0007.finish <|
    gateSourcePiece0008.finish <|
    gateSourcePiece0009.finish <|
    gateSourcePiece0010.finish <|
    gateSourcePiece0011.finish <|
    gateSourcePiece0012.finish <|
    gateSourcePiece0013.finish <|
    gateSourcePiece0014.finish <|
    gateSourcePiece0015.finish <|
    gateSourcePiece0016.finish <|
    gateSourcePiece0017.finish <|
    gateSourcePiece0018.finish <|
    gateSourcePiece0019.finish <|
    gateSourcePiece0020.finish <|
    gateSourcePiece0021.finish <|
    gateSourcePiece0022.finish <|
    gateSourcePiece0023.finish <|
    gateSourcePiece0024.finish <|
    gateSourcePiece0025.finish <|
    gateSourcePiece0026.finish <|
    gateSourcePiece0027.finish <|
    gateSourcePiece0028.finish <|
    gateSourcePiece0029.finish <|
    gateSourcePiece0030.finish <|
    gateSourcePiece0031.finish <|
    gateSourcePiece0032.finish <|
    gateSourcePiece0033.finish <|
    gateSourcePiece0034.finish <|
    gateSourcePiece0035.finish <|
    gateSourcePiece0036.finish <|
    gateSourcePiece0037.finish <|
    gateSourcePiece0038.finish <|
    gateSourcePiece0039.finish <|
    gateSourcePiece0040.finish <|
    gateSourcePiece0041.finish <|
    gateSourcePiece0042.finish <|
    gateSourcePiece0043.finish <|
    gateSourcePiece0044.finish <|
    gateSourcePiece0045.finish <|
    gateSourcePiece0046.finish <|
    gateSourcePiece0047.finish <|
    gateSourcePiece0048.finish <|
    gateSourcePiece0049.finish <|
    gateSourcePiece0050.finish <|
    gateSourcePiece0051.finish <|
    gateSourcePiece0052.finish <|
    gateSourcePiece0053.finish <|
    gateSourcePiece0054.finish <|
    gateSourcePiece0055.finish <|
    gateSourcePiece0056.finish <|
    gateSourcePiece0057.finish <|
    gateSourcePiece0058.finish <|
    gateSourcePiece0059.finish <|
    gateSourcePiece0060.finish <|
    gateSourcePiece0061.finish <|
    gateSourcePiece0062.finish <|
    gateSourcePiece0063.finish <|
    gateSourcePiece0064.finish <|
    gateSourcePiece0065.finish <|
    gateSourcePiece0066.finish <|
    gateSourcePiece0067.finish <|
    gateSourcePiece0068.finish <|
    gateSourcePiece0069.finish <|
    gateSourcePiece0070.finish <|
    gateSourcePiece0071.finish <|
    gateSourcePiece0072.finish <|
    gateSourcePiece0073.finish <|
    gateSourcePiece0074.finish <|
    gateSourcePiece0075.finish <|
    gateSourcePiece0076.finish <|
    gateSourcePiece0077.finish <|
    gateSourcePiece0078.finish <|
    gateSourcePiece0079.finish <|
    gateSourcePiece0080.finish <|
    gateSourcePiece0081.finish <|
    gateSourcePiece0082.finish <|
    gateSourcePiece0083.finish <|
    gateSourcePiece0084.finish <|
    gateSourcePiece0085.finish <|
    gateSourcePiece0086.finish <|
    gateSourcePiece0087.finish <|
    gateSourcePiece0088.finish <|
    gateSourcePiece0089.finish <|
    gateSourcePiece0090.finish <|
    gateSourcePiece0091.finish <|
    gateSourcePiece0092.finish <|
    gateSourcePiece0093.finish <|
    gateSourcePiece0094.finish <|
    gateSourcePiece0095.finish <|
    gateSourcePiece0096.finish <|
    gateSourcePiece0097.finish <|
    gateSourcePiece0098.finish <|
    gateSourcePiece0099.finish <|
    gateSourcePiece0100.finish <|
    gateSourcePiece0101.finish <|
    gateSourcePiece0102.finish <|
    gateSourcePiece0103.finish <|
    gateSourcePiece0104.finish <|
    gateSourcePiece0105.finish <|
    gateSourcePiece0106.finish <|
    gateSourcePiece0107.finish <|
    gateSourcePiece0108.finish <|
    gateSourcePiece0109.finish <|
    gateSourcePiece0110.finish <|
    gateSourcePiece0111.finish <|
    gateSourcePiece0112.finish <|
    gateSourcePiece0113.finish <|
    gateSourcePiece0114.finish <|
    gateSourcePiece0115.finish <|
    gateSourcePiece0116.finish <|
    gateSourcePiece0117.finish <|
    gateSourcePiece0118.finish <|
    gateSourcePiece0119.finish <|
    gateSourcePiece0120.finish <|
    gateSourcePiece0121.finish <|
    gateSourcePiece0122.finish <|
    gateSourcePiece0123.finish <|
    gateSourcePiece0124.finish <|
    gateSourcePiece0125.finish <|
    gateSourcePiece0126.finish <|
    gateSourcePiece0127.finish <|
    gateSourcePiece0128.finish <|
    gateSourcePiece0129.finish <|
    gateSourcePiece0130.finish <|
    gateSourcePiece0131.finish <|
    gateSourcePiece0132.finish <|
    gateSourcePiece0133.finish <|
    gateSourcePiece0134.finish <|
    gateSourcePiece0135.finish <|
    gateSourcePiece0136.finish <|
    gateSourcePiece0137.finish <|
    gateSourcePiece0138.finish <|
    gateSourcePiece0139.finish <|
    gateSourcePiece0140.finish <|
    gateSourcePiece0141.finish <|
    gateSourcePiece0142.finish <|
    gateSourcePiece0143.finish <|
    gateSourcePiece0144.finish <|
    gateSourcePiece0145.finish <|
    gateSourcePiece0146.finish <|
    gateSourcePiece0147.finish <|
    gateSourcePiece0148.finish <|
    gateSourcePiece0149.finish <|
    gateSourcePiece0150.finish <|
    gateSourcePiece0151.finish <|
    gateSourcePiece0152.finish <|
    gateSourcePiece0153.finish <|
    gateSourcePiece0154.finish <|
    gateSourcePiece0155.finish <|
    gateSourcePiece0156.finish <|
    gateSourcePiece0157.finish <|
    gateSourcePiece0158.finish <|
    gateSourcePiece0159.finish <|
    gateSourcePiece0160.finish <|
    gateSourcePiece0161.finish <|
    gateSourcePiece0162.finish <|
    gateSourcePiece0163.finish <|
    gateSourcePiece0164.finish <|
    gateSourcePiece0165.finish <|
    gateSourcePiece0166.finish <|
    gateSourcePiece0167.finish <|
    gateSourcePiece0168.finish <|
    gateSourcePiece0169.finish <|
    gateSourcePiece0170.finish <|
    gateSourcePiece0171.finish <|
    gateSourcePiece0172.finish <|
    gateSourcePiece0173.finish <|
    gateSourcePiece0174.finish <|
    gateSourcePiece0175.finish <|
    gateSourcePiece0176.finish <|
    gateSourcePiece0177.finish <|
    gateSourcePiece0178.finish <|
    gateSourcePiece0179.finish <|
    gateSourcePiece0180.finish <|
    gateSourcePiece0181.finish <|
    gateSourcePiece0182.finish <|
    gateSourcePiece0183.finish <|
    gateSourcePiece0184.finish <|
    gateSourcePiece0185.finish <|
    gateSourcePiece0186.finish <|
    gateSourcePiece0187.finish <|
    gateSourcePiece0188.finish <|
    gateSourcePiece0189.finish <|
    gateSourcePiece0190.finish <|
    gateSourcePiece0191.finish <|
    gateSourcePiece0192.finish <|
    gateSourcePiece0193.finish <|
    gateSourcePiece0194.finish <|
    suffix

end Zcash.Snark.ZeroKnowledge
