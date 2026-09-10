import Zcash.Snark.ZeroKnowledge.ActionAdviceSourcePrefix

/-!
# Bounded continuation of the original Action source

The module retains the source left by the preceding certificate and composes
checked continuations for it. The remaining suffix is still an explicit
obligation of the complete Action certificate.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option stderrAsMessages false
set_option trace.Zcash.adviceSourceCertificate true

private noncomputable def piece000 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (actionAdviceSourcePrefix.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece001 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece000.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece002 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece001.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece003 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece002.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece004 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece003.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece005 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece004.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece006 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece005.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece007 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece006.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece008 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece007.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece009 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece008.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece010 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece009.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece011 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece010.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece012 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece011.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece013 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece012.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece014 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece013.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece015 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece014.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece016 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece015.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece017 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece016.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece018 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece017.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece019 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece018.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece020 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece019.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece021 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece020.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece022 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece021.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece023 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece022.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece024 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece023.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece025 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece024.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece026 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece025.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece027 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece026.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece028 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece027.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece029 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece028.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece030 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece029.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece031 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece030.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece032 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece031.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece033 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece032.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece034 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece033.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece035 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece034.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece036 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece035.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece037 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece036.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece038 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece037.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece039 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece038.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece040 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece039.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece041 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece040.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece042 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece041.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece043 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece042.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece044 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece043.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece045 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece044.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece046 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece045.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece047 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece046.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece048 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece047.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece049 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece048.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece050 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece049.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece051 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece050.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece052 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece051.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece053 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece052.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece054 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece053.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece055 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece054.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece056 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece055.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece057 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece056.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece058 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece057.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece059 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece058.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece060 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece059.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece061 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece060.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece062 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece061.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece063 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece062.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece064 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece063.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece065 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece064.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece066 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece065.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece067 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece066.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece068 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece067.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece069 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece068.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece070 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece069.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece071 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece070.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece072 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece071.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece073 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece072.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece074 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece073.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece075 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece074.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece076 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece075.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece077 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece076.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece078 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece077.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece079 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece078.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece080 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece079.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece081 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece080.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece082 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece081.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece083 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece082.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece084 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece083.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece085 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece084.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece086 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece085.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece087 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece086.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece088 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece087.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece089 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece088.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece090 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece089.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece091 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece090.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece092 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece091.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece093 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece092.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece094 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece093.remaining) := by
  certify_source_advice_piece 8 8

private noncomputable def piece095 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece094.remaining) := by
  certify_source_advice_piece 8 8

/-- The accumulated source certificate continues from its exact remaining instructions. -/
noncomputable def actionAdviceSourceChunk000 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) actionAdviceSourcePrograms where
  remaining := piece095.remaining
  finish suffix :=
    actionAdviceSourcePrefix.finish <|
    piece000.finish <|
    piece001.finish <|
    piece002.finish <|
    piece003.finish <|
    piece004.finish <|
    piece005.finish <|
    piece006.finish <|
    piece007.finish <|
    piece008.finish <|
    piece009.finish <|
    piece010.finish <|
    piece011.finish <|
    piece012.finish <|
    piece013.finish <|
    piece014.finish <|
    piece015.finish <|
    piece016.finish <|
    piece017.finish <|
    piece018.finish <|
    piece019.finish <|
    piece020.finish <|
    piece021.finish <|
    piece022.finish <|
    piece023.finish <|
    piece024.finish <|
    piece025.finish <|
    piece026.finish <|
    piece027.finish <|
    piece028.finish <|
    piece029.finish <|
    piece030.finish <|
    piece031.finish <|
    piece032.finish <|
    piece033.finish <|
    piece034.finish <|
    piece035.finish <|
    piece036.finish <|
    piece037.finish <|
    piece038.finish <|
    piece039.finish <|
    piece040.finish <|
    piece041.finish <|
    piece042.finish <|
    piece043.finish <|
    piece044.finish <|
    piece045.finish <|
    piece046.finish <|
    piece047.finish <|
    piece048.finish <|
    piece049.finish <|
    piece050.finish <|
    piece051.finish <|
    piece052.finish <|
    piece053.finish <|
    piece054.finish <|
    piece055.finish <|
    piece056.finish <|
    piece057.finish <|
    piece058.finish <|
    piece059.finish <|
    piece060.finish <|
    piece061.finish <|
    piece062.finish <|
    piece063.finish <|
    piece064.finish <|
    piece065.finish <|
    piece066.finish <|
    piece067.finish <|
    piece068.finish <|
    piece069.finish <|
    piece070.finish <|
    piece071.finish <|
    piece072.finish <|
    piece073.finish <|
    piece074.finish <|
    piece075.finish <|
    piece076.finish <|
    piece077.finish <|
    piece078.finish <|
    piece079.finish <|
    piece080.finish <|
    piece081.finish <|
    piece082.finish <|
    piece083.finish <|
    piece084.finish <|
    piece085.finish <|
    piece086.finish <|
    piece087.finish <|
    piece088.finish <|
    piece089.finish <|
    piece090.finish <|
    piece091.finish <|
    piece092.finish <|
    piece093.finish <|
    piece094.finish <|
    piece095.finish <|
    suffix

end Zcash.Snark.ZeroKnowledge
