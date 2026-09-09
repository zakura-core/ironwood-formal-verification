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

theorem sharedSelector_complete :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7), (18, "second", 7)] = true := by kernel_rfl

theorem rejectsMissingSharedGate :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7)] = false := by kernel_rfl

theorem rejectsWrongGateRow :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7), (18, "second", 8)] = false := by kernel_rfl

theorem unrelatedSelector_preserved :
    gateActivationCoverageScan [(18, "first")] [(19, 7)] [] = true := by kernel_rfl

theorem lookupMasters_complete :
    lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3), (1, 4)] = true := by kernel_rfl

theorem rejectsMissingLookupMaster :
    lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3)] = false := by kernel_rfl

theorem rejectsWrongLookupRow :
    lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3), (1, 5)] = false := by kernel_rfl

theorem storedSharedSelector_complete :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7), (18, "second", 7)] = true := by check_activation_coverage

theorem storedRejectsMissingSharedGate : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7)] = true := by check_activation_coverage
  trivial

theorem storedRejectsWrongGateRow : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7), (18, "second", 8)] = true := by check_activation_coverage
  trivial

theorem storedUnrelatedSelector_preserved :
    gateActivationCoverageScan [(18, "first")] [(19, 7)] [] = true := by check_activation_coverage

theorem storedLookupMasters_complete :
    lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3), (1, 4)] = true := by
  check_activation_coverage

theorem storedRejectsMissingLookupMaster : True := by
  fail_if_success
    have _invalid : lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3)] = true := by
      check_activation_coverage
  trivial

theorem storedRejectsWrongLookupRow : True := by
  fail_if_success
    have _invalid : lookupActivationCoverageScan [0, 1] [(0, 3), (1, 4)] [(0, 3), (1, 5)] = true := by
      check_activation_coverage
  trivial

theorem indexedSharedSelector_complete :
    gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
      [(18, "first", 7), (18, "second", 7)] = true := by
  rw [← gateIndexedCoverageScan_original]
  check_activation_coverage

theorem indexedRejectsMissingSharedGate : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7)] = true := by
      rw [← gateIndexedCoverageScan_original]
      check_activation_coverage
  trivial

theorem indexedRejectsUnknownName : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7), (18, "unregistered", 7)] = true := by
      rw [← gateIndexedCoverageScan_original]
      check_activation_coverage
  trivial

theorem indexedRejectsWrongRow : True := by
  fail_if_success
    have _invalid : gateActivationCoverageScan [(18, "first"), (18, "second")] [(18, 7)]
        [(18, "first", 7), (18, "second", 8)] = true := by
      rw [← gateIndexedCoverageScan_original]
      check_activation_coverage
  trivial

theorem indexedEqualNamesDifferentSelectors_complete :
    gateActivationCoverageScan [(18, "same"), (19, "same")] [(18, 7), (19, 8)]
      [(18, "same", 7), (19, "same", 8)] = true := by
  rw [← gateIndexedCoverageScan_original]
  check_activation_coverage

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
