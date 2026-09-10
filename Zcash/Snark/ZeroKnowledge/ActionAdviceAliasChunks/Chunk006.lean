import Zcash.Snark.ZeroKnowledge.ActionAdviceAliasChunks.Chunk005

/-!
# Bounded continuation of the Action alias scan

The continuation retains the accumulated map and every unprocessed source entry.
Its completion requires the original scan to succeed from that exact state.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option stderrAsMessages false
set_option trace.Zcash.adviceMapScan true

private noncomputable def piece000 :
    AdviceMapScanPiece adviceAliasMapStep actionAdviceAliasChunk005.remainingRoots
      actionAdviceAliasChunk005.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece001 :
    AdviceMapScanPiece adviceAliasMapStep piece000.remainingRoots
      piece000.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece002 :
    AdviceMapScanPiece adviceAliasMapStep piece001.remainingRoots
      piece001.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece003 :
    AdviceMapScanPiece adviceAliasMapStep piece002.remainingRoots
      piece002.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece004 :
    AdviceMapScanPiece adviceAliasMapStep piece003.remainingRoots
      piece003.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece005 :
    AdviceMapScanPiece adviceAliasMapStep piece004.remainingRoots
      piece004.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece006 :
    AdviceMapScanPiece adviceAliasMapStep piece005.remainingRoots
      piece005.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece007 :
    AdviceMapScanPiece adviceAliasMapStep piece006.remainingRoots
      piece006.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece008 :
    AdviceMapScanPiece adviceAliasMapStep piece007.remainingRoots
      piece007.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece009 :
    AdviceMapScanPiece adviceAliasMapStep piece008.remainingRoots
      piece008.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece010 :
    AdviceMapScanPiece adviceAliasMapStep piece009.remainingRoots
      piece009.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece011 :
    AdviceMapScanPiece adviceAliasMapStep piece010.remainingRoots
      piece010.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece012 :
    AdviceMapScanPiece adviceAliasMapStep piece011.remainingRoots
      piece011.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece013 :
    AdviceMapScanPiece adviceAliasMapStep piece012.remainingRoots
      piece012.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece014 :
    AdviceMapScanPiece adviceAliasMapStep piece013.remainingRoots
      piece013.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece015 :
    AdviceMapScanPiece adviceAliasMapStep piece014.remainingRoots
      piece014.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece016 :
    AdviceMapScanPiece adviceAliasMapStep piece015.remainingRoots
      piece015.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece017 :
    AdviceMapScanPiece adviceAliasMapStep piece016.remainingRoots
      piece016.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece018 :
    AdviceMapScanPiece adviceAliasMapStep piece017.remainingRoots
      piece017.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece019 :
    AdviceMapScanPiece adviceAliasMapStep piece018.remainingRoots
      piece018.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece020 :
    AdviceMapScanPiece adviceAliasMapStep piece019.remainingRoots
      piece019.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece021 :
    AdviceMapScanPiece adviceAliasMapStep piece020.remainingRoots
      piece020.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece022 :
    AdviceMapScanPiece adviceAliasMapStep piece021.remainingRoots
      piece021.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece023 :
    AdviceMapScanPiece adviceAliasMapStep piece022.remainingRoots
      piece022.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece024 :
    AdviceMapScanPiece adviceAliasMapStep piece023.remainingRoots
      piece023.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece025 :
    AdviceMapScanPiece adviceAliasMapStep piece024.remainingRoots
      piece024.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece026 :
    AdviceMapScanPiece adviceAliasMapStep piece025.remainingRoots
      piece025.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece027 :
    AdviceMapScanPiece adviceAliasMapStep piece026.remainingRoots
      piece026.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece028 :
    AdviceMapScanPiece adviceAliasMapStep piece027.remainingRoots
      piece027.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece029 :
    AdviceMapScanPiece adviceAliasMapStep piece028.remainingRoots
      piece028.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece030 :
    AdviceMapScanPiece adviceAliasMapStep piece029.remainingRoots
      piece029.remainingEntries := by
  check_advice_map_piece 32

private noncomputable def piece031 :
    AdviceMapScanPiece adviceAliasMapStep piece030.remainingRoots
      piece030.remainingEntries := by
  check_advice_map_piece 32

/-- The original alias scan follows from its remaining entries and retained map. -/
noncomputable def actionAdviceAliasChunk006 :
    AdviceMapScanPiece adviceAliasMapStep ∅
      (adviceAliasAddressData (actionAdviceSourceCertificate.annotations.map (fun entry => (entry.1.instruction, entry.2)))) where
  remainingRoots := piece031.remainingRoots
  remainingEntries := piece031.remainingEntries
  finish suffix :=
    actionAdviceAliasChunk005.finish <|
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
    suffix

end Zcash.Snark.ZeroKnowledge
