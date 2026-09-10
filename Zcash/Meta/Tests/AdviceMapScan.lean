import Zcash.Meta.AdviceMapScan
import Zcash.Meta.AdviceSourceCertificate
import Zcash.Meta.AxiomCheck
import Zcash.Meta.KernelRfl

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

/-- The read scan accepts a dependency written earlier in the instruction stream, exercising
sequential availability. -/
theorem earlierRead_available :
    adviceSupportMapPlan id ∅ readChain.readCertificate.annotations = true := by
  rw [adviceSupportMapPlan_eq_scan]
  check_advice_map_scan

def futureRead : AdviceSourceCertificate (F := Fp)
    [(⟨⟨0⟩, 0, instanceGet ⟨0⟩ 0⟩, none),
     (⟨⟨1⟩, 0, .ofFExpr (.expr (.of 0 1 (⟨0⟩ : Column .advice)))⟩, none)] := by
  certify_source_advice

/-- The read scan rejects a dependency written only later, guarding the witness-construction order. -/
theorem rejectsFutureRead : True := by
  fail_if_success
    have _invalid : adviceSupportMapPlan id ∅ futureRead.readCertificate.annotations = true := by
      rw [adviceSupportMapPlan_eq_scan]
      check_advice_map_scan
  trivial

def firstAddress : AdviceAddress := ((⟨0⟩ : Column .advice).toAny, 0)
def secondAddress : AdviceAddress := ((⟨1⟩ : Column .advice).toAny, 0)

/-- Copies with the same established root may revisit an address, exercising the permitted alias
case. -/
theorem equalRootCopy_available :
    adviceAliasMapPlan ∅ [(firstAddress, none), (secondAddress, some firstAddress),
      (firstAddress, some secondAddress)] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

/-- A fresh write cannot overwrite an existing address, guarding the alias scan against collisions. -/
theorem rejectsFreshWriteCollision : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan ∅ [(firstAddress, none), (firstAddress, none)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

/-- An address cannot be assigned incompatible copy roots, exercising alias-conflict rejection. -/
theorem rejectsConflictingRoot : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan ∅ [(firstAddress, none), (secondAddress, none),
        (firstAddress, some secondAddress)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

/-- An advice copy cannot read a source absent from the map, guarding sequential copy availability. -/
theorem rejectsUnavailableSource : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan ∅ [(firstAddress, some secondAddress)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

/-- An instance cell is an available immutable copy source, exercising the non-advice source case. -/
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

/-- An opaque scalar builder can introduce a fresh write, checking that callback opacity does not
block valid alias data. -/
theorem opaqueScalarBuilder_freshWrite :
    adviceAliasMapPlan ∅ [(firstAddress, scalarBuilderCopyTag)] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

/-- An opaque scalar builder cannot conceal a write collision, guarding the alias check across
source barriers. -/
theorem opaqueScalarBuilder_rejectsCollision : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan ∅
        [(firstAddress, none), (firstAddress, scalarBuilderCopyTag)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

section Population
set_option maxRecDepth 10000

private def populationSource : List (AdviceAddress × Option AdviceAddress) :=
  (List.range 512).map fun row => (((⟨7⟩ : Column .advice).toAny, row), none)

private def populationPiece00 : AdviceMapScanPiece adviceAliasMapStep
    ∅ populationSource := by
  check_advice_map_piece 32

private def populationPiece01 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece00.remainingRoots populationPiece00.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece02 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece01.remainingRoots populationPiece01.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece03 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece02.remainingRoots populationPiece02.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece04 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece03.remainingRoots populationPiece03.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece05 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece04.remainingRoots populationPiece04.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece06 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece05.remainingRoots populationPiece05.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece07 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece06.remainingRoots populationPiece06.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece08 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece07.remainingRoots populationPiece07.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece09 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece08.remainingRoots populationPiece08.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece10 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece09.remainingRoots populationPiece09.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece11 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece10.remainingRoots populationPiece10.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece12 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece11.remainingRoots populationPiece11.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece13 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece12.remainingRoots populationPiece12.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece14 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece13.remainingRoots populationPiece13.remainingEntries := by
  check_advice_map_piece 32

private def populationPiece15 : AdviceMapScanPiece adviceAliasMapStep
    populationPiece14.remainingRoots populationPiece14.remainingEntries := by
  check_advice_map_piece 32

/-- A stored map with 512 unrelated assignments exercises populated-map scans.
The setup is constructed separately so policy checks use their budget on the scan. -/
def populatedRoots : AdviceAliasMap := populationPiece15.remainingRoots

end Population

/-- The separately constructed map retains all 512 entries required by the stress cases. -/
theorem populatedRoots_size : populatedRoots.size = 512 := by
  kernel_rfl

set_option maxRecDepth 10000 in
/-- Every original row remains mapped to itself, guarding the populated-map setup against data loss. -/
theorem populatedRoots_containsRows :
    (List.range 512).all (fun row =>
      let address : AdviceAddress := ((⟨7⟩ : Column .advice).toAny, row)
      adviceAliasMapLookup populatedRoots address == some address) = true := by
  kernel_rfl

set_option maxRecDepth 10000 in
/-- A scalar builder can add a fresh address to an existing map, exercising the populated-map path. -/
theorem opaqueScalarBuilder_afterPopulatedMap :
    adviceAliasMapPlan populatedRoots [(firstAddress, scalarBuilderCopyTag)] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

set_option maxRecDepth 10000 in
/-- A scalar builder cannot overwrite a populated-map entry, guarding the nonempty-map collision
case. -/
theorem opaqueScalarBuilder_rejectsPopulatedCollision : True := by
  fail_if_success
    have _invalid : adviceAliasMapPlan populatedRoots
        [(firstAddress, none), (firstAddress, scalarBuilderCopyTag)] = true := by
      rw [adviceAliasMapPlan_eq_scan]
      check_advice_map_scan
  trivial

set_option maxRecDepth 10000 in
/-- Established equal-root copies remain valid in a populated map, exercising alias reuse with prior
state. -/
theorem equalRootCopy_afterPopulatedMap :
    adviceAliasMapPlan populatedRoots [(firstAddress, none), (secondAddress, some firstAddress),
      (firstAddress, some secondAddress)] = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

set_option maxRecDepth 10000 in
/-- Prior map entries do not permit conflicting roots, exercising rejection after unrelated writes. -/
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

/-- The read scan accepts an available cell through an opaque placement wrapper, exercising source
normalization. -/
theorem opaquePlacedRead_available :
    adviceSupportMapPlan id (adviceAliasMapInsert ∅ firstAddress firstAddress)
      [opaqueReadAnnotation 0] = true := by
  rw [adviceSupportMapPlan_eq_scan]
  check_advice_map_scan

/-- An opaque placement wrapper cannot hide an unavailable read, guarding source normalization
against false positives. -/
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
assert_axioms Zcash.Meta.Tests.AdviceMapScan.populatedRoots_size
assert_axioms Zcash.Meta.Tests.AdviceMapScan.populatedRoots_containsRows
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaqueScalarBuilder_afterPopulatedMap
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaqueScalarBuilder_rejectsPopulatedCollision
assert_axioms Zcash.Meta.Tests.AdviceMapScan.equalRootCopy_afterPopulatedMap
assert_axioms Zcash.Meta.Tests.AdviceMapScan.rejectsPopulatedConflictingRoot

assert_axioms Zcash.Meta.Tests.AdviceMapScan.placedReadCellSource
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaqueReadAnnotation
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaquePlacedRead_available
assert_axioms Zcash.Meta.Tests.AdviceMapScan.opaquePlacedRead_rejectsUnavailable

end Zcash.Meta.Tests.AdviceMapScan
