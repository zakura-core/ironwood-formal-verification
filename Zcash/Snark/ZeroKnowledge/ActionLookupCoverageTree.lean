import Zcash.Snark.ZeroKnowledge.ActionLookupCoverageData
import Zcash.Meta.KernelRfl

/-!
# Complete comparison tree for the original Action lookup check

The retained tree states preserve every original lookup label. The remaining
fold must be completed before the configured master predicates are checked.
-/

namespace Zcash.Snark.ZeroKnowledge
attribute [local instance] lexOrd
attribute [local irreducible] coverageTreeFold
set_option maxRecDepth 50000
set_option stderrAsMessages false
set_option trace.Zcash.activationCoverage true

private noncomputable def piece000 :
    CoverageTreePiece compare actionLookupCoverageLabels.entries lookupCoverageEmpty := by
  certify_coverage_tree_piece 64

private noncomputable def piece001 :
    CoverageTreePiece compare piece000.remainingEntries piece000.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece002 :
    CoverageTreePiece compare piece001.remainingEntries piece001.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece003 :
    CoverageTreePiece compare piece002.remainingEntries piece002.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece004 :
    CoverageTreePiece compare piece003.remainingEntries piece003.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece005 :
    CoverageTreePiece compare piece004.remainingEntries piece004.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece006 :
    CoverageTreePiece compare piece005.remainingEntries piece005.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece007 :
    CoverageTreePiece compare piece006.remainingEntries piece006.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece008 :
    CoverageTreePiece compare piece007.remainingEntries piece007.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece009 :
    CoverageTreePiece compare piece008.remainingEntries piece008.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece010 :
    CoverageTreePiece compare piece009.remainingEntries piece009.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece011 :
    CoverageTreePiece compare piece010.remainingEntries piece010.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece012 :
    CoverageTreePiece compare piece011.remainingEntries piece011.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece013 :
    CoverageTreePiece compare piece012.remainingEntries piece012.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece014 :
    CoverageTreePiece compare piece013.remainingEntries piece013.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece015 :
    CoverageTreePiece compare piece014.remainingEntries piece014.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece016 :
    CoverageTreePiece compare piece015.remainingEntries piece015.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece017 :
    CoverageTreePiece compare piece016.remainingEntries piece016.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece018 :
    CoverageTreePiece compare piece017.remainingEntries piece017.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece019 :
    CoverageTreePiece compare piece018.remainingEntries piece018.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece020 :
    CoverageTreePiece compare piece019.remainingEntries piece019.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece021 :
    CoverageTreePiece compare piece020.remainingEntries piece020.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece022 :
    CoverageTreePiece compare piece021.remainingEntries piece021.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece023 :
    CoverageTreePiece compare piece022.remainingEntries piece022.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece024 :
    CoverageTreePiece compare piece023.remainingEntries piece023.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece025 :
    CoverageTreePiece compare piece024.remainingEntries piece024.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece026 :
    CoverageTreePiece compare piece025.remainingEntries piece025.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece027 :
    CoverageTreePiece compare piece026.remainingEntries piece026.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece028 :
    CoverageTreePiece compare piece027.remainingEntries piece027.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece029 :
    CoverageTreePiece compare piece028.remainingEntries piece028.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece030 :
    CoverageTreePiece compare piece029.remainingEntries piece029.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece031 :
    CoverageTreePiece compare piece030.remainingEntries piece030.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece032 :
    CoverageTreePiece compare piece031.remainingEntries piece031.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece033 :
    CoverageTreePiece compare piece032.remainingEntries piece032.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece034 :
    CoverageTreePiece compare piece033.remainingEntries piece033.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece035 :
    CoverageTreePiece compare piece034.remainingEntries piece034.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece036 :
    CoverageTreePiece compare piece035.remainingEntries piece035.remainingTree := by
  certify_coverage_tree_piece 64

private noncomputable def piece037 :
    CoverageTreePiece compare piece036.remainingEntries piece036.remainingTree := by
  certify_coverage_tree_piece 64

/-- The lookup tree retains its complete source-fold obligation until the remainder is closed. -/
noncomputable def actionLookupCoverageTree :
    CoverageTreePiece compare actionLookupCoverageLabels.entries lookupCoverageEmpty where
  remainingEntries := piece037.remainingEntries
  remainingTree := piece037.remainingTree
  finish final rest :=
    piece000.finish final <|
    piece001.finish final <|
    piece002.finish final <|
    piece003.finish final <|
    piece004.finish final <|
    piece005.finish final <|
    piece006.finish final <|
    piece007.finish final <|
    piece008.finish final <|
    piece009.finish final <|
    piece010.finish final <|
    piece011.finish final <|
    piece012.finish final <|
    piece013.finish final <|
    piece014.finish final <|
    piece015.finish final <|
    piece016.finish final <|
    piece017.finish final <|
    piece018.finish final <|
    piece019.finish final <|
    piece020.finish final <|
    piece021.finish final <|
    piece022.finish final <|
    piece023.finish final <|
    piece024.finish final <|
    piece025.finish final <|
    piece026.finish final <|
    piece027.finish final <|
    piece028.finish final <|
    piece029.finish final <|
    piece030.finish final <|
    piece031.finish final <|
    piece032.finish final <|
    piece033.finish final <|
    piece034.finish final <|
    piece035.finish final <|
    piece036.finish final <|
    piece037.finish final <|
    rest

/-- Every original lookup label has been consumed before the final tree is used. -/
private theorem tree_remainder_empty : actionLookupCoverageTree.remainingEntries = [] := by
  kernel_rfl

/-- Completing the retained fold identifies exactly the tree of the complete original source. -/
private theorem tree_eq :
    lookupCoverageTree actionLookupCoverageLabels.entries = actionLookupCoverageTree.remainingTree := by
  apply actionLookupCoverageTree.finish
  simp only [tree_remainder_empty, coverageTreeFold, List.foldl_nil]

/-- Each configured master retains every one of its original activated rows. -/
private theorem predicates_checked :
    coverageListAll
      (lookupCoveragePredicate actionCoverageActivations.entries actionLookupCoverageTree.remainingTree)
      actionLookupCoverageMasters.entries = true := by
  check_coverage_predicates

/-- The separately certified data and tree establish the complete original lookup scan. -/
theorem actionLookupCoverage_check :
    lookupActivationCoverageScan actionLookupCoverageMasters.entries actionCoverageActivations.entries
      actionLookupCoverageLabels.entries = true := by
  exact lookupActivationCoverageScan_stored _ _ _ _ _ _ _
    rfl rfl rfl tree_eq predicates_checked

end Zcash.Snark.ZeroKnowledge
