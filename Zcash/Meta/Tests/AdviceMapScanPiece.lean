import Zcash.Meta.AdviceMapScan
import Zcash.Meta.AxiomCheck
import Zcash.Meta.KernelRfl

/-!
# Advice-map state across declaration boundaries

The positive chain revisits a written address through the same alias root.
Negative cases retain a rejected fresh write after a valid first segment, and
reject attempts to complete that failed suffix.
-/

namespace Zcash.Meta.Tests.AdviceMapScanPiece
open Halo2 Zcash.Snark.ZeroKnowledge

def firstAddress : AdviceAddress := ((⟨0⟩ : Column .advice).toAny, 0)
def secondAddress : AdviceAddress := ((⟨1⟩ : Column .advice).toAny, 0)

def source : List (AdviceAddress × Option AdviceAddress) :=
  [(firstAddress, none), (secondAddress, some firstAddress), (firstAddress, some secondAddress)]

def untouched : AdviceMapScanPiece adviceAliasMapStep ∅ source := by
  check_advice_map_piece 0

def first : AdviceMapScanPiece adviceAliasMapStep ∅ source := by
  check_advice_map_piece 1

def second : AdviceMapScanPiece adviceAliasMapStep first.remainingRoots first.remainingEntries := by
  check_advice_map_piece 1

def third : AdviceMapScanPiece adviceAliasMapStep second.remainingRoots second.remainingEntries := by
  check_advice_map_piece 1

/-- The next segment receives the established root, preventing a reset of the alias history. -/
theorem first_retainsRoot :
    adviceAliasMapLookup first.remainingRoots firstAddress = some firstAddress := by
  kernel_rfl

/-- Doing no work retains both the initial map and the complete source as an obligation. -/
theorem zeroSteps_retainsState : untouched.remainingRoots = ∅ ∧ untouched.remainingEntries = source := by
  constructor <;> kernel_rfl

/-- A complete alias chain remains valid when its transitions cross declaration boundaries. -/
theorem complete_accepts : adviceMapScan adviceAliasMapStep ∅ source = true :=
  first.finish (second.finish (third.finish rfl))

def collisionPrefix : AdviceMapScanPiece adviceAliasMapStep ∅
    [(firstAddress, none), (firstAddress, none)] := by
  check_advice_map_piece 1

/-- A fresh-write collision is rejected after the earlier write has been checked and stored. -/
theorem rejectsCollisionAfterPrefix : True := by
  fail_if_success
    have _invalid : AdviceMapScanPiece adviceAliasMapStep
        collisionPrefix.remainingRoots collisionPrefix.remainingEntries := by
      check_advice_map_piece 1
  trivial

/-- A failed remaining scan cannot be discharged when the checked prefix is completed. -/
theorem rejectsFailedSuffix : True := by
  fail_if_success
    have _invalid : adviceMapScan adviceAliasMapStep ∅
        [(firstAddress, none), (firstAddress, none)] = true := collisionPrefix.finish rfl
  trivial

assert_computable Zcash.Meta.Tests.AdviceMapScanPiece.firstAddress
assert_computable Zcash.Meta.Tests.AdviceMapScanPiece.secondAddress
assert_computable Zcash.Meta.Tests.AdviceMapScanPiece.source
assert_computable Zcash.Meta.Tests.AdviceMapScanPiece.untouched +choice
assert_computable Zcash.Meta.Tests.AdviceMapScanPiece.first +choice
assert_computable Zcash.Meta.Tests.AdviceMapScanPiece.second +choice
assert_computable Zcash.Meta.Tests.AdviceMapScanPiece.third +choice
assert_computable Zcash.Meta.Tests.AdviceMapScanPiece.collisionPrefix +choice
assert_axioms Zcash.Meta.Tests.AdviceMapScanPiece.first_retainsRoot
assert_axioms Zcash.Meta.Tests.AdviceMapScanPiece.zeroSteps_retainsState
assert_axioms Zcash.Meta.Tests.AdviceMapScanPiece.complete_accepts
assert_axioms Zcash.Meta.Tests.AdviceMapScanPiece.rejectsCollisionAfterPrefix
assert_axioms Zcash.Meta.Tests.AdviceMapScanPiece.rejectsFailedSuffix

end Zcash.Meta.Tests.AdviceMapScanPiece
