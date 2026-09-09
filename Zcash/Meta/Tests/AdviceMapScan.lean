import Zcash.Meta.AdviceMapScan
import Zcash.Meta.AdviceSourceCertificate
import Zcash.Meta.AxiomCheck

/-!
# Adversarial checks across advice-map certificate boundaries

Every entry forces a piece boundary. Successful chains cross those boundaries;
future reads, fresh-write collisions, and conflicting alias roots must still
fail after earlier pieces have already been checked.
-/

namespace Zcash.Meta.Tests.AdviceMapScan
open Halo2 Witgen Zcash.Circuits Zcash.Snark.ZeroKnowledge

set_option Zcash.adviceMapScan.chunkEntries 1

def readChain : AdviceSourceCertificate (F := Fp)
    [(⟨⟨0⟩, 0, instanceGet ⟨0⟩ 0⟩, none),
     (⟨⟨1⟩, 0, .ofFExpr (.expr (.of 0 0 (⟨0⟩ : Column .advice)))⟩, none)] := by
  certify_source_advice

theorem earlierRead_available :
    adviceSupportMapPlan id ∅ readChain.readCertificate.annotations = true := by
  rw [adviceSupportMapPlan_eq_scan]
  check_advice_map_scan

def futureRead : AdviceSourceCertificate (F := Fp)
    [(⟨⟨0⟩, 0, instanceGet ⟨0⟩ 0⟩, none),
     (⟨⟨1⟩, 0, .ofFExpr (.expr (.of 0 1 (⟨0⟩ : Column .advice)))⟩, none)] := by
  certify_source_advice

theorem rejectsFutureRead : True := by
  fail_if_success
    have _invalid : adviceSupportMapPlan id ∅ futureRead.readCertificate.annotations = true := by
      rw [adviceSupportMapPlan_eq_scan]
      check_advice_map_scan
  trivial

def firstAddress : AdviceAddress := ((⟨0⟩ : Column .advice).toAny, 0)
def secondAddress : AdviceAddress := ((⟨1⟩ : Column .advice).toAny, 0)

theorem equalRootCopy_available :
    adviceAliasMapPlan ∅ [(firstAddress, none), (secondAddress, some firstAddress),
      (firstAddress, some secondAddress)] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

theorem rejectsFreshWriteCollision : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan ∅ [(firstAddress, none), (firstAddress, none)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

theorem rejectsConflictingRoot : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan ∅ [(firstAddress, none), (secondAddress, none),
        (firstAddress, some secondAddress)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

theorem rejectsUnavailableSource : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan ∅ [(firstAddress, some secondAddress)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

theorem immutableSource_available :
    adviceAliasMapPlan ∅ [(firstAddress, some ((⟨7⟩ : Column .instance).toAny, 17))] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

assert_computable Zcash.Meta.Tests.AdviceMapScan.readChain +choice
assert_axioms Zcash.Meta.Tests.AdviceMapScan.earlierRead_available
assert_computable Zcash.Meta.Tests.AdviceMapScan.futureRead +choice
assert_axioms Zcash.Meta.Tests.AdviceMapScan.rejectsFutureRead
assert_computable Zcash.Meta.Tests.AdviceMapScan.firstAddress
assert_computable Zcash.Meta.Tests.AdviceMapScan.secondAddress
assert_axioms Zcash.Meta.Tests.AdviceMapScan.equalRootCopy_available
assert_axioms Zcash.Meta.Tests.AdviceMapScan.rejectsFreshWriteCollision
assert_axioms Zcash.Meta.Tests.AdviceMapScan.rejectsConflictingRoot
assert_axioms Zcash.Meta.Tests.AdviceMapScan.rejectsUnavailableSource
assert_axioms Zcash.Meta.Tests.AdviceMapScan.immutableSource_available

end Zcash.Meta.Tests.AdviceMapScan
