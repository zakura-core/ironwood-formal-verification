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

/-- The original source is named once so piece types share its program expression. -/
private def valueSourcePrograms (input : Var ValueCommit.Inputs Fp) :
    List (PlacedAdviceProgram Fp × Option AdviceAddress) :=
    (circuitAdviceAliases (F := Fp)
        (fun region => actionRegionStartsCertificate.getD region 0)
        (actionNativeAdviceCopySource (fun region => actionRegionStartsCertificate.getD region 0))
        (((ValueCommit.circuit orchardBases.valueCommitV orchardBases.valueCommitR).call
          (actionConfig.eccConfig.mulFixedShort, actionConfig.eccConfig.mulFixedFull,
            actionConfig.eccConfig.add) input).operations 266) 266)

-- Each declaration checks at most 64 source reductions and eight instructions.
-- The final continuation is closed only after the complete source is exhausted.
private noncomputable def valueSourcePiece000 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) (valueSourcePrograms input) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece001 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece000 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece002 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece001 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece003 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece002 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece004 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece003 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece005 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece004 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece006 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece005 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece007 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece006 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece008 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece007 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece009 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece008 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece010 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece009 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece011 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece010 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece012 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece011 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece013 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece012 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece014 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece013 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece015 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece014 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece016 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece015 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece017 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece016 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece018 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece017 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece019 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece018 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece020 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece019 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece021 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece020 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece022 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece021 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece023 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece022 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece024 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece023 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece025 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece024 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece026 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece025 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece027 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece026 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece028 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece027 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece029 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece028 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece030 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece029 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece031 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece030 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece032 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece031 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece033 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece032 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece034 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece033 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece035 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece034 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece036 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece035 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece037 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece036 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece038 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece037 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece039 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece038 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece040 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece039 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece041 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece040 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece042 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece041 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece043 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece042 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece044 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece043 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece045 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece044 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece046 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece045 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece047 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece046 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece048 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece047 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece049 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece048 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece050 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece049 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece051 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece050 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece052 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece051 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece053 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece052 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece054 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece053 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece055 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece054 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece056 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece055 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece057 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece056 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece058 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece057 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece059 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece058 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece060 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece059 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece061 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece060 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece062 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece061 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece063 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece062 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece064 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece063 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece065 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece064 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece066 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece065 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece067 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece066 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece068 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece067 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece069 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece068 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece070 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece069 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece071 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece070 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece072 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece071 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece073 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece072 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece074 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece073 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece075 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece074 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece076 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece075 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece077 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece076 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece078 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece077 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece079 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece078 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece080 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece079 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece081 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece080 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece082 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece081 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece083 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece082 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece084 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece083 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece085 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece084 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece086 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece085 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece087 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece086 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece088 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece087 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece089 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece088 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece090 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece089 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece091 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece090 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece092 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece091 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece093 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece092 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece094 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece093 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece095 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece094 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece096 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece095 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece097 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece096 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece098 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece097 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece099 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece098 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece100 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece099 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece101 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece100 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece102 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece101 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece103 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece102 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece104 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece103 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece105 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece104 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece106 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece105 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece107 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece106 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece108 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece107 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece109 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece108 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece110 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece109 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece111 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece110 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece112 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece111 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece113 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece112 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece114 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece113 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece115 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece114 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece116 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece115 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece117 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece116 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece118 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece117 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece119 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece118 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece120 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece119 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece121 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece120 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece122 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece121 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece123 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece122 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece124 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece123 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece125 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece124 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece126 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece125 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece127 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece126 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece128 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece127 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece129 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece128 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece130 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece129 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece131 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece130 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece132 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece131 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece133 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece132 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece134 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece133 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece135 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece134 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece136 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece135 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece137 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece136 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece138 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece137 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece139 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece138 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece140 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece139 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece141 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece140 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece142 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece141 input).remaining) := by
  certify_source_advice_piece 64 8

private noncomputable def valueSourcePiece143 (input : Var ValueCommit.Inputs Fp) :
    SourceCertificatePiece (AdviceSourceCertificate (F := Fp)) ((valueSourcePiece142 input).remaining) := by
  certify_source_advice_piece 64 8

/-- Semantic read annotations for every original value-commitment instruction. -/
noncomputable def actionValueSourceCertificate (input : Var ValueCommit.Inputs Fp) :
    AdviceSourceCertificate (F := Fp)
      (circuitAdviceAliases (F := Fp)
        (fun region => actionRegionStartsCertificate.getD region 0)
        (actionNativeAdviceCopySource (fun region => actionRegionStartsCertificate.getD region 0))
        (((ValueCommit.circuit orchardBases.valueCommitV orchardBases.valueCommitR).call
          (actionConfig.eccConfig.mulFixedShort, actionConfig.eccConfig.mulFixedFull,
            actionConfig.eccConfig.add) input).operations 266) 266) := by
  change AdviceSourceCertificate (valueSourcePrograms input)
  exact
    (valueSourcePiece000 input).finish <|
    (valueSourcePiece001 input).finish <|
    (valueSourcePiece002 input).finish <|
    (valueSourcePiece003 input).finish <|
    (valueSourcePiece004 input).finish <|
    (valueSourcePiece005 input).finish <|
    (valueSourcePiece006 input).finish <|
    (valueSourcePiece007 input).finish <|
    (valueSourcePiece008 input).finish <|
    (valueSourcePiece009 input).finish <|
    (valueSourcePiece010 input).finish <|
    (valueSourcePiece011 input).finish <|
    (valueSourcePiece012 input).finish <|
    (valueSourcePiece013 input).finish <|
    (valueSourcePiece014 input).finish <|
    (valueSourcePiece015 input).finish <|
    (valueSourcePiece016 input).finish <|
    (valueSourcePiece017 input).finish <|
    (valueSourcePiece018 input).finish <|
    (valueSourcePiece019 input).finish <|
    (valueSourcePiece020 input).finish <|
    (valueSourcePiece021 input).finish <|
    (valueSourcePiece022 input).finish <|
    (valueSourcePiece023 input).finish <|
    (valueSourcePiece024 input).finish <|
    (valueSourcePiece025 input).finish <|
    (valueSourcePiece026 input).finish <|
    (valueSourcePiece027 input).finish <|
    (valueSourcePiece028 input).finish <|
    (valueSourcePiece029 input).finish <|
    (valueSourcePiece030 input).finish <|
    (valueSourcePiece031 input).finish <|
    (valueSourcePiece032 input).finish <|
    (valueSourcePiece033 input).finish <|
    (valueSourcePiece034 input).finish <|
    (valueSourcePiece035 input).finish <|
    (valueSourcePiece036 input).finish <|
    (valueSourcePiece037 input).finish <|
    (valueSourcePiece038 input).finish <|
    (valueSourcePiece039 input).finish <|
    (valueSourcePiece040 input).finish <|
    (valueSourcePiece041 input).finish <|
    (valueSourcePiece042 input).finish <|
    (valueSourcePiece043 input).finish <|
    (valueSourcePiece044 input).finish <|
    (valueSourcePiece045 input).finish <|
    (valueSourcePiece046 input).finish <|
    (valueSourcePiece047 input).finish <|
    (valueSourcePiece048 input).finish <|
    (valueSourcePiece049 input).finish <|
    (valueSourcePiece050 input).finish <|
    (valueSourcePiece051 input).finish <|
    (valueSourcePiece052 input).finish <|
    (valueSourcePiece053 input).finish <|
    (valueSourcePiece054 input).finish <|
    (valueSourcePiece055 input).finish <|
    (valueSourcePiece056 input).finish <|
    (valueSourcePiece057 input).finish <|
    (valueSourcePiece058 input).finish <|
    (valueSourcePiece059 input).finish <|
    (valueSourcePiece060 input).finish <|
    (valueSourcePiece061 input).finish <|
    (valueSourcePiece062 input).finish <|
    (valueSourcePiece063 input).finish <|
    (valueSourcePiece064 input).finish <|
    (valueSourcePiece065 input).finish <|
    (valueSourcePiece066 input).finish <|
    (valueSourcePiece067 input).finish <|
    (valueSourcePiece068 input).finish <|
    (valueSourcePiece069 input).finish <|
    (valueSourcePiece070 input).finish <|
    (valueSourcePiece071 input).finish <|
    (valueSourcePiece072 input).finish <|
    (valueSourcePiece073 input).finish <|
    (valueSourcePiece074 input).finish <|
    (valueSourcePiece075 input).finish <|
    (valueSourcePiece076 input).finish <|
    (valueSourcePiece077 input).finish <|
    (valueSourcePiece078 input).finish <|
    (valueSourcePiece079 input).finish <|
    (valueSourcePiece080 input).finish <|
    (valueSourcePiece081 input).finish <|
    (valueSourcePiece082 input).finish <|
    (valueSourcePiece083 input).finish <|
    (valueSourcePiece084 input).finish <|
    (valueSourcePiece085 input).finish <|
    (valueSourcePiece086 input).finish <|
    (valueSourcePiece087 input).finish <|
    (valueSourcePiece088 input).finish <|
    (valueSourcePiece089 input).finish <|
    (valueSourcePiece090 input).finish <|
    (valueSourcePiece091 input).finish <|
    (valueSourcePiece092 input).finish <|
    (valueSourcePiece093 input).finish <|
    (valueSourcePiece094 input).finish <|
    (valueSourcePiece095 input).finish <|
    (valueSourcePiece096 input).finish <|
    (valueSourcePiece097 input).finish <|
    (valueSourcePiece098 input).finish <|
    (valueSourcePiece099 input).finish <|
    (valueSourcePiece100 input).finish <|
    (valueSourcePiece101 input).finish <|
    (valueSourcePiece102 input).finish <|
    (valueSourcePiece103 input).finish <|
    (valueSourcePiece104 input).finish <|
    (valueSourcePiece105 input).finish <|
    (valueSourcePiece106 input).finish <|
    (valueSourcePiece107 input).finish <|
    (valueSourcePiece108 input).finish <|
    (valueSourcePiece109 input).finish <|
    (valueSourcePiece110 input).finish <|
    (valueSourcePiece111 input).finish <|
    (valueSourcePiece112 input).finish <|
    (valueSourcePiece113 input).finish <|
    (valueSourcePiece114 input).finish <|
    (valueSourcePiece115 input).finish <|
    (valueSourcePiece116 input).finish <|
    (valueSourcePiece117 input).finish <|
    (valueSourcePiece118 input).finish <|
    (valueSourcePiece119 input).finish <|
    (valueSourcePiece120 input).finish <|
    (valueSourcePiece121 input).finish <|
    (valueSourcePiece122 input).finish <|
    (valueSourcePiece123 input).finish <|
    (valueSourcePiece124 input).finish <|
    (valueSourcePiece125 input).finish <|
    (valueSourcePiece126 input).finish <|
    (valueSourcePiece127 input).finish <|
    (valueSourcePiece128 input).finish <|
    (valueSourcePiece129 input).finish <|
    (valueSourcePiece130 input).finish <|
    (valueSourcePiece131 input).finish <|
    (valueSourcePiece132 input).finish <|
    (valueSourcePiece133 input).finish <|
    (valueSourcePiece134 input).finish <|
    (valueSourcePiece135 input).finish <|
    (valueSourcePiece136 input).finish <|
    (valueSourcePiece137 input).finish <|
    (valueSourcePiece138 input).finish <|
    (valueSourcePiece139 input).finish <|
    (valueSourcePiece140 input).finish <|
    (valueSourcePiece141 input).finish <|
    (valueSourcePiece142 input).finish <|
    (valueSourcePiece143 input).finish <|
    AdviceSourceCertificate.nil

/-- Every input gives the same complete 1,083-instruction source certificate. -/
theorem actionValueSource_annotationCount (input : Var ValueCommit.Inputs Fp) :
    (actionValueSourceCertificate input).annotations.length = 1083 := by
  kernel_rfl

end Zcash.Snark.ZeroKnowledge
