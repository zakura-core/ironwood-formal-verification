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


/-- The scalar builder hides its IR constructor behind an opaque source equation. -/
def scalarBuilderCopyTag : Option AdviceAddress :=
  let program := Zcash.Circuits.Ecc.MulComplete.zWit
    (.of 0 0 (⟨0⟩ : Column .advice)) (pure (fun _ => Witgen.BExprOver.false)) 0
  match program with
  | .native _ => none
  | .ir _ _ => witnessCopyAddress id program

theorem opaqueScalarBuilder_freshWrite :
    adviceAliasMapPlan ∅ [(firstAddress, scalarBuilderCopyTag)] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

theorem opaqueScalarBuilder_rejectsCollision : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan ∅
        [(firstAddress, none), (firstAddress, scalarBuilderCopyTag)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

/-- A pre-existing map exercises normalization after many unrelated assignments. -/
def populatedRoots : AdviceAliasMap :=
  (List.range 512).foldl (fun roots row =>
    let address : AdviceAddress := ((⟨7⟩ : Column .advice).toAny, row)
    adviceAliasMapInsert roots address address) ∅

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem opaqueScalarBuilder_afterPopulatedMap :
    adviceAliasMapPlan populatedRoots [(firstAddress, scalarBuilderCopyTag)] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem opaqueScalarBuilder_rejectsPopulatedCollision : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan populatedRoots
        [(firstAddress, none), (firstAddress, scalarBuilderCopyTag)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem equalRootCopy_afterPopulatedMap :
    adviceAliasMapPlan populatedRoots [(firstAddress, none), (secondAddress, some firstAddress),
      (firstAddress, some secondAddress)] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem rejectsPopulatedConflictingRoot : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan populatedRoots [(firstAddress, none), (secondAddress, none),
        (firstAddress, some secondAddress)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial


opaque placedReadCellSource (row : ℕ) :
    { cell : AssignedCell Fp // cell = .of 0 row (⟨0⟩ : Column .advice) } := ⟨_, rfl⟩

/-- An over-approximate read certificate keeps the opaque cell in its original data. -/
noncomputable def opaqueReadAnnotation (row : ℕ) : SupportedAdviceProgram Fp where
  instruction := ⟨⟨1⟩, 0, .ofFExpr (.const 0)⟩
  reads := [(placedReadCellSource row).val]
  support := by
    intro left right _
    simp [WitgenIROver.ofFExpr, WitgenIROver.eval, VExprOver.eval, FExprOver.eval]

theorem opaquePlacedRead_available :
    adviceSupportMapPlan id (adviceAliasMapInsert ∅ firstAddress firstAddress)
      [opaqueReadAnnotation 0] = true := by
  rw [adviceSupportMapPlan_eq_scan]
  check_advice_map_scan

theorem opaquePlacedRead_rejectsUnavailable : True := by
  fail_if_success
    have _invalid : adviceSupportMapPlan id (adviceAliasMapInsert ∅ firstAddress firstAddress)
        [opaqueReadAnnotation 1] = true := by
      rw [adviceSupportMapPlan_eq_scan]
      check_advice_map_scan
  trivial

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

assert_computable Zcash.Meta.Tests.AdviceMapScan.scalarBuilderCopyTag +choice
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaqueScalarBuilder_freshWrite
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaqueScalarBuilder_rejectsCollision
assert_computable Zcash.Meta.Tests.AdviceMapScan.populatedRoots +choice
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaqueScalarBuilder_afterPopulatedMap
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaqueScalarBuilder_rejectsPopulatedCollision
assert_axioms Zcash.Meta.Tests.AdviceMapScan.equalRootCopy_afterPopulatedMap
assert_axioms Zcash.Meta.Tests.AdviceMapScan.rejectsPopulatedConflictingRoot

assert_axioms Zcash.Meta.Tests.AdviceMapScan.placedReadCellSource
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaqueReadAnnotation
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaquePlacedRead_available
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaquePlacedRead_rejectsUnavailable

end Zcash.Meta.Tests.AdviceMapScan
