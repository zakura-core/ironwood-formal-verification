import Zcash.Snark.ZeroKnowledge.ActivationCoverageScan
import Zcash.Meta.KernelRfl
import Zcash.Meta.ActivationCoverage
import Zcash.Meta.AxiomCheck

/-!
# Kernel computation and rejection cases for activation coverage

These closed checks require actual kernel reduction, in addition to the generic
equivalence theorem. Shared selectors must retain both gate names, and a correct
name or master at a different row must not satisfy an activation.
-/

namespace Zcash.Meta.Tests.ActivationCoverageScan
open Zcash.Snark.ZeroKnowledge

/-- Both gates sharing a selector are retained, exercising coverage of multiple names at one active
row. -/
theorem sharedSelector_complete :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7), (18, "second", 7)] = true := by kernel_rfl

/-- Omitting one gate sharing a selector fails coverage, even when the other gate is present. -/
theorem rejectsMissingSharedGate :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7)] = false := by kernel_rfl

/-- A gate entry at another row cannot certify the active row, guarding against row-insensitive
coverage. -/
theorem rejectsWrongGateRow :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7), (18, "second", 8)] = false := by kernel_rfl

/-- An activation of an unrelated selector creates no obligation for this gate, checking selector
filtering. -/
theorem unrelatedSelector_preserved :
    gateActivationCoverageScan [(18, "first")] [(19, 7)] [] = true := by kernel_rfl

/-- Every active lookup master has its matching source row, providing a positive lookup-coverage
case. -/
theorem lookupMasters_complete :
    lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3), (1, 4)] = true := by kernel_rfl

/-- An omitted active lookup master fails coverage, checking that all masters are required. -/
theorem rejectsMissingLookupMaster :
    lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3)] = false := by kernel_rfl

/-- A lookup entry at another row fails coverage, checking that the master alone is insufficient. -/
theorem rejectsWrongLookupRow :
    lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3), (1, 5)] = false := by kernel_rfl

/-- The certificate tactic accepts both gates sharing a selector, exercising its positive
shared-selector case. -/
theorem storedSharedSelector_complete :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7), (18, "second", 7)] = true := by check_activation_coverage

/-- The certificate tactic rejects a shared selector with one gate missing, guarding its rejection
path. -/
theorem storedRejectsMissingSharedGate : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7)] = true := by check_activation_coverage
  trivial

/-- The certificate tactic rejects a gate recorded at the wrong row, guarding row-sensitive
validation. -/
theorem storedRejectsWrongGateRow : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7), (18, "second", 8)] = true := by check_activation_coverage
  trivial

/-- The certificate tactic ignores unrelated selectors, exercising its filtering path. -/
theorem storedUnrelatedSelector_preserved :
    gateActivationCoverageScan [(18, "first")] [(19, 7)] [] = true := by check_activation_coverage

/-- The certificate tactic accepts a complete lookup-master trace, exercising positive lookup
validation. -/
theorem storedLookupMasters_complete :
    lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3), (1, 4)] = true := by
  check_activation_coverage

/-- The certificate tactic rejects a missing lookup master, guarding its completeness check. -/
theorem storedRejectsMissingLookupMaster : True := by
  fail_if_success
    have _invalid : lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3)] = true := by
      check_activation_coverage
  trivial

/-- The certificate tactic rejects a lookup at the wrong row, guarding row-sensitive validation. -/
theorem storedRejectsWrongLookupRow : True := by
  fail_if_success
    have _invalid : lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3), (1, 5)] = true := by
      check_activation_coverage
  trivial

/-- Indexing gate names preserves coverage of both gates sharing a selector, checking the indexed
scan. -/
theorem indexedSharedSelector_complete :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7), (18, "second", 7)] = true := by
  rw [← gateIndexedCoverageScan_original]
  check_activation_coverage

/-- The indexed scan rejects an omitted gate sharing a selector, guarding against collapsing shared
gates. -/
theorem indexedRejectsMissingSharedGate : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7)] = true := by
      rw [← gateIndexedCoverageScan_original]
      check_activation_coverage
  trivial

/-- An unregistered gate name cannot replace a configured gate, guarding the indexed name lookup. -/
theorem indexedRejectsUnknownName : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7), (18, "unregistered", 7)] = true := by
      rw [← gateIndexedCoverageScan_original]
      check_activation_coverage
  trivial

/-- The indexed scan rejects a correct gate name at the wrong row, preserving activation locality. -/
theorem indexedRejectsWrongRow : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7), (18, "second", 8)] = true := by
      rw [← gateIndexedCoverageScan_original]
      check_activation_coverage
  trivial

/-- Equal gate names on different selectors remain distinct coverage obligations, exercising the
composite index. -/
theorem indexedEqualNamesDifferentSelectors_complete :
    gateActivationCoverageScan [(18, "same"), (19, "same")] [(18, 7), (19, 8)]
      [(18, "same", 7), (19, "same", 8)] = true := by
  rw [← gateIndexedCoverageScan_original]
  check_activation_coverage

/-- A matching gate name under another selector cannot discharge coverage, guarding against
name-only indexing. -/
theorem indexedRejectsEqualNameWrongSelector : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "same"), (19, "same")] [(18, 7), (19, 8)]
        [(18, "same", 7), (18, "same", 8)] = true := by
      rw [← gateIndexedCoverageScan_original]
      check_activation_coverage
  trivial

assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.sharedSelector_complete
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.rejectsMissingSharedGate
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.rejectsWrongGateRow
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.unrelatedSelector_preserved
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.lookupMasters_complete
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.rejectsMissingLookupMaster
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.rejectsWrongLookupRow
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.storedSharedSelector_complete
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.storedRejectsMissingSharedGate
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.storedRejectsWrongGateRow
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.storedUnrelatedSelector_preserved
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.storedLookupMasters_complete
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.storedRejectsMissingLookupMaster
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.storedRejectsWrongLookupRow
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.indexedSharedSelector_complete
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.indexedRejectsMissingSharedGate
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.indexedRejectsUnknownName
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.indexedRejectsWrongRow
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.indexedEqualNamesDifferentSelectors_complete
assert_axioms Zcash.Meta.Tests.ActivationCoverageScan.indexedRejectsEqualNameWrongSelector

end Zcash.Meta.Tests.ActivationCoverageScan
