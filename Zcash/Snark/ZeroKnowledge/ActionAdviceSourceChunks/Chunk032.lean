import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceChunks.Chunk031

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
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (actionAdviceSourceChunk031.remaining) := by
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

/-- The accumulated source certificate continues from its exact remaining instructions. -/
noncomputable def actionAdviceSourceChunk032 :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) actionAdviceSourcePrograms where
  remaining := piece021.remaining
  finish suffix :=
    actionAdviceSourceChunk031.finish <|
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
    suffix

end Zcash.Snark.ZeroKnowledge
