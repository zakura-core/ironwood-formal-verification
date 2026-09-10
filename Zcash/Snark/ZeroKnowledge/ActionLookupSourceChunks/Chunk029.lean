import Zcash.Snark.ZeroKnowledge.ActionLookupSourceChunks.Chunk028

/-!
# Bounded continuation of the original lookup source

The module retains the source left by the preceding certificate and composes
checked continuations for it. The remaining suffix is still an explicit
obligation of the complete lookup certificate.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option stderrAsMessages false
set_option trace.Zcash.sourceListCertificate true

private noncomputable def piece000 :
    SourceCertificatePiece SourceListCertificate (actionLookupSourceChunk028.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece001 :
    SourceCertificatePiece SourceListCertificate (piece000.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece002 :
    SourceCertificatePiece SourceListCertificate (piece001.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece003 :
    SourceCertificatePiece SourceListCertificate (piece002.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece004 :
    SourceCertificatePiece SourceListCertificate (piece003.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece005 :
    SourceCertificatePiece SourceListCertificate (piece004.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece006 :
    SourceCertificatePiece SourceListCertificate (piece005.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece007 :
    SourceCertificatePiece SourceListCertificate (piece006.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece008 :
    SourceCertificatePiece SourceListCertificate (piece007.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece009 :
    SourceCertificatePiece SourceListCertificate (piece008.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece010 :
    SourceCertificatePiece SourceListCertificate (piece009.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece011 :
    SourceCertificatePiece SourceListCertificate (piece010.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece012 :
    SourceCertificatePiece SourceListCertificate (piece011.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece013 :
    SourceCertificatePiece SourceListCertificate (piece012.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece014 :
    SourceCertificatePiece SourceListCertificate (piece013.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece015 :
    SourceCertificatePiece SourceListCertificate (piece014.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece016 :
    SourceCertificatePiece SourceListCertificate (piece015.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece017 :
    SourceCertificatePiece SourceListCertificate (piece016.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece018 :
    SourceCertificatePiece SourceListCertificate (piece017.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece019 :
    SourceCertificatePiece SourceListCertificate (piece018.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece020 :
    SourceCertificatePiece SourceListCertificate (piece019.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece021 :
    SourceCertificatePiece SourceListCertificate (piece020.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece022 :
    SourceCertificatePiece SourceListCertificate (piece021.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece023 :
    SourceCertificatePiece SourceListCertificate (piece022.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece024 :
    SourceCertificatePiece SourceListCertificate (piece023.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece025 :
    SourceCertificatePiece SourceListCertificate (piece024.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece026 :
    SourceCertificatePiece SourceListCertificate (piece025.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece027 :
    SourceCertificatePiece SourceListCertificate (piece026.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece028 :
    SourceCertificatePiece SourceListCertificate (piece027.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece029 :
    SourceCertificatePiece SourceListCertificate (piece028.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece030 :
    SourceCertificatePiece SourceListCertificate (piece029.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece031 :
    SourceCertificatePiece SourceListCertificate (piece030.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece032 :
    SourceCertificatePiece SourceListCertificate (piece031.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece033 :
    SourceCertificatePiece SourceListCertificate (piece032.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece034 :
    SourceCertificatePiece SourceListCertificate (piece033.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece035 :
    SourceCertificatePiece SourceListCertificate (piece034.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece036 :
    SourceCertificatePiece SourceListCertificate (piece035.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece037 :
    SourceCertificatePiece SourceListCertificate (piece036.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece038 :
    SourceCertificatePiece SourceListCertificate (piece037.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece039 :
    SourceCertificatePiece SourceListCertificate (piece038.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece040 :
    SourceCertificatePiece SourceListCertificate (piece039.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece041 :
    SourceCertificatePiece SourceListCertificate (piece040.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece042 :
    SourceCertificatePiece SourceListCertificate (piece041.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece043 :
    SourceCertificatePiece SourceListCertificate (piece042.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece044 :
    SourceCertificatePiece SourceListCertificate (piece043.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece045 :
    SourceCertificatePiece SourceListCertificate (piece044.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece046 :
    SourceCertificatePiece SourceListCertificate (piece045.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece047 :
    SourceCertificatePiece SourceListCertificate (piece046.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece048 :
    SourceCertificatePiece SourceListCertificate (piece047.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece049 :
    SourceCertificatePiece SourceListCertificate (piece048.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece050 :
    SourceCertificatePiece SourceListCertificate (piece049.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece051 :
    SourceCertificatePiece SourceListCertificate (piece050.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece052 :
    SourceCertificatePiece SourceListCertificate (piece051.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece053 :
    SourceCertificatePiece SourceListCertificate (piece052.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece054 :
    SourceCertificatePiece SourceListCertificate (piece053.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece055 :
    SourceCertificatePiece SourceListCertificate (piece054.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece056 :
    SourceCertificatePiece SourceListCertificate (piece055.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece057 :
    SourceCertificatePiece SourceListCertificate (piece056.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece058 :
    SourceCertificatePiece SourceListCertificate (piece057.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece059 :
    SourceCertificatePiece SourceListCertificate (piece058.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece060 :
    SourceCertificatePiece SourceListCertificate (piece059.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece061 :
    SourceCertificatePiece SourceListCertificate (piece060.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece062 :
    SourceCertificatePiece SourceListCertificate (piece061.remaining) := by
  certify_source_list_piece 16 64

private noncomputable def piece063 :
    SourceCertificatePiece SourceListCertificate (piece062.remaining) := by
  certify_source_list_piece 16 64

/-- The accumulated source certificate continues from its exact remaining lookup labels. -/
noncomputable def actionLookupSourceChunk029 :
    SourceCertificatePiece SourceListCertificate actionLookupSourceLabels where
  remaining := piece063.remaining
  finish suffix :=
    actionLookupSourceChunk028.finish <|
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
