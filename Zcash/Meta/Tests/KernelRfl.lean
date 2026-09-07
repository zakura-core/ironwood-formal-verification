import Zcash.Meta.KernelRfl
import Zcash.Meta.AxiomCheck

/-!
# Kernel-reflexivity certificate checks

The negative cases run inside `fail_if_success`: a false computation or a changed
callback argument must be rejected before the tactic returns successfully.
-/

namespace Zcash.Meta.Tests.KernelRfl

theorem closedReduction : (List.range 8).reverse = [7, 6, 5, 4, 3, 2, 1, 0] := by
  kernel_rfl

theorem arbitraryCallback (callback : List Nat → List Nat) :
    (if (List.range 8).length = 8 then callback [1, 2] else callback []) = callback [1, 2] := by
  kernel_rfl

theorem rejectsFalseComputation : True := by
  fail_if_success
    have _invalid : (List.range 8).length = 7 := by kernel_rfl
  trivial

theorem rejectsChangedCallback (_callback : Nat → Nat) : True := by
  fail_if_success
    have _invalid : _callback 0 = _callback 1 := by kernel_rfl
  trivial

theorem rejectsNonEquality : True := by
  fail_if_success kernel_rfl
  trivial

assert_axioms Zcash.Meta.Tests.KernelRfl.closedReduction
assert_axioms Zcash.Meta.Tests.KernelRfl.arbitraryCallback
assert_axioms Zcash.Meta.Tests.KernelRfl.rejectsFalseComputation
assert_axioms Zcash.Meta.Tests.KernelRfl.rejectsChangedCallback
assert_axioms Zcash.Meta.Tests.KernelRfl.rejectsNonEquality

end Zcash.Meta.Tests.KernelRfl
