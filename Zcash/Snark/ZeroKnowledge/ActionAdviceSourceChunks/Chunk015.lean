import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceChunks.Chunk014

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
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (actionAdviceSourceChunk014.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece001 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece000.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece002 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece001.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece003 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece002.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece004 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece003.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece005 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece004.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece006 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece005.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece007 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece006.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece008 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece007.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece009 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece008.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece010 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece009.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece011 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece010.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece012 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece011.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece013 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece012.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece014 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece013.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece015 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece014.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece016 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece015.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece017 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece016.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece018 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece017.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece019 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece018.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece020 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece019.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece021 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece020.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece022 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece021.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece023 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece022.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece024 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece023.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece025 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece024.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece026 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece025.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece027 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece026.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece028 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece027.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece029 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece028.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece030 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece029.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece031 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece030.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece032 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece031.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece033 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece032.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece034 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece033.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece035 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece034.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece036 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece035.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece037 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece036.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece038 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece037.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece039 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece038.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece040 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece039.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece041 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece040.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece042 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece041.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece043 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece042.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece044 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece043.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece045 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece044.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece046 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece045.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece047 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece046.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece048 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece047.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece049 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece048.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece050 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece049.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece051 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece050.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece052 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece051.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece053 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece052.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece054 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece053.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece055 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece054.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece056 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece055.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece057 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece056.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece058 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece057.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece059 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece058.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece060 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece059.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece061 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece060.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece062 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece061.remaining) := by
  certify_source_advice_piece 16 8

private noncomputable def piece063 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (piece062.remaining) := by
  certify_source_advice_piece 16 8

/-- The accumulated source certificate continues from its exact remaining instructions. -/
noncomputable def actionAdviceSourceChunk015 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) actionAdviceSourcePrograms where
  remaining := piece063.remaining
  finish suffix :=
    actionAdviceSourceChunk014.finish <|
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
    suffix

end Zcash.Snark.ZeroKnowledge
