import Zcash.Meta.ActivationCoverage
import Zcash.Meta.AxiomCheck
import Zcash.Meta.KernelRfl

/-!
# Metadata and comparison-tree continuation checks

The tests retain source order, repeated entries, and the accumulated comparison
tree across declaration boundaries. Failed remaining folds and configured
predicates cannot complete the original check.
-/

namespace Zcash.Meta.Tests.ActivationCoveragePieces
open Zcash.Snark.ZeroKnowledge
attribute [local instance] lexOrd

noncomputable def metadata (offset : ℕ) :
    SourceListCertificate [(offset + 1, 7), (offset, 3), (offset + 1, 7)] := by
  certify_coverage_data

def source : List (ℕ × ℕ) := [(2, 3), (1, 7), (2, 3)]

noncomputable def untouched : CoverageTreePiece compare source lookupCoverageEmpty := by
  certify_coverage_tree_piece 0

noncomputable def first : CoverageTreePiece compare source lookupCoverageEmpty := by
  certify_coverage_tree_piece 1

noncomputable def second :
    CoverageTreePiece compare first.remainingEntries first.remainingTree := by
  certify_coverage_tree_piece 1

noncomputable def last :
    CoverageTreePiece compare second.remainingEntries second.remainingTree := by
  certify_coverage_tree_piece 1

/-- Normalization retains parameterized entries, their order, and their repetition. -/
theorem metadata_retains_source (offset : ℕ) :
    (metadata offset).entries = [(offset + 1, 7), (offset, 3), (offset + 1, 7)] := by
  kernel_rfl

/-- A zero-step continuation retains the initial tree and every pending label. -/
theorem zeroSteps_retainsState :
    untouched.remainingTree = lookupCoverageEmpty ∧ untouched.remainingEntries = source := by
  constructor <;> kernel_rfl

/-- A checked insertion remains in the tree passed to the next declaration. -/
theorem first_retainsState :
    first.remainingTree.contains (2, 3) = true ∧ first.remainingEntries = source.drop 1 := by
  constructor <;> kernel_rfl

/-- Completing the final remainder constructs exactly the tree of the complete original source. -/
theorem complete_tree : lookupCoverageTree source = last.remainingTree :=
  first.finish _ (second.finish _ (last.finish _ rfl))

/-- An unfinished nonempty fold cannot be discharged by supplying an empty final tree. -/
theorem rejectsWrongRemainder : True := by
  fail_if_success
    have _invalid : lookupCoverageTree source = lookupCoverageEmpty :=
      first.finish _ rfl
  trivial

/-- Every configured entry is checked when the conjunction is assembled separately. -/
theorem predicates_accept : coverageListAll (fun value : ℕ => decide (value < 5)) [1, 3] = true := by
  check_coverage_predicates

/-- A later rejected entry cannot be hidden by an earlier successful predicate. -/
theorem predicates_reject : True := by
  fail_if_success
    have _invalid : coverageListAll (fun value : ℕ => decide (value < 5)) [1, 7] = true := by
      check_coverage_predicates
  trivial

opaque sourceValue : { value : ℕ // value = 2 } := ⟨2, rfl⟩

noncomputable def opaqueMetadata :
    SourceListCertificate [(sourceValue.val, 0), (sourceValue.val, 1)] := by
  certify_coverage_data

noncomputable def opaqueFirst :
    CoverageTreePiece compare opaqueMetadata.entries lookupCoverageEmpty := by
  certify_coverage_tree_piece 1

noncomputable def opaqueSecond :
    CoverageTreePiece compare opaqueFirst.remainingEntries opaqueFirst.remainingTree := by
  certify_coverage_tree_piece 1

/-- A source-owned opaque equality may remain in a certificate's index without corrupting the next tree state. -/
theorem opaqueSource_complete : lookupCoverageTree opaqueMetadata.entries = opaqueSecond.remainingTree :=
  opaqueFirst.finish _ (opaqueSecond.finish _ rfl)

assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.metadata
assert_computable Zcash.Meta.Tests.ActivationCoveragePieces.source
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.untouched
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.first
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.second
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.last
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.metadata_retains_source
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.zeroSteps_retainsState
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.first_retainsState
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.complete_tree
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.rejectsWrongRemainder
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.predicates_accept
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.predicates_reject
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.sourceValue
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.opaqueMetadata
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.opaqueFirst
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.opaqueSecond
assert_axioms Zcash.Meta.Tests.ActivationCoveragePieces.opaqueSource_complete

end Zcash.Meta.Tests.ActivationCoveragePieces
