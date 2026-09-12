import Zcash.Snark.ZeroKnowledge.ActionMulNativeCopies
import Zcash.Snark.ZeroKnowledge.ActionNativeCopyIntervals
import Zcash.Snark.ZeroKnowledge.NativeCopyLift

/-!
# Native-copy provenance through the complete original Action

The original address-integrity multiplier occupies region 297. All surrounding
source intervals have no native annotations. The proof follows the actual
subcircuit operations and their checked region-count bridges, then opens the
opaque Action only through its implementation equation. Together with the IR
copy recognizer, this establishes every annotation's evaluator semantics.

This source certificate does not assert that the global alias or read plans
succeed; those remain separate premises of the witness-execution theorem.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 8192

/-- The original multiplication call uses the certified main region and unannotated overflow regions. -/
theorem actionMulCall_nativeCopiesSound (place : RegionIndex → ℕ)
    (input : Var Ecc.Mul.Inputs Fp) :
    CircuitNativeCopiesSound place (actionNativeAdviceCopySource place)
      ((Ecc.Mul.mul.call actionConfig.eccConfig.mul input).operations 297) 297 := by
  rw [FormalCircuit.call_operations]
  change CircuitNativeCopiesSound place (actionNativeAdviceCopySource place)
    ((Ecc.Mul.synthesize actionConfig.eccConfig.mul input).operations 297) 297
  simp only [Ecc.Mul.synthesize, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, circuitNativeCopiesSound_append]
  constructor
  · rw [circuitNativeCopiesSound_toFormal, FormalRegionCircuit.call_operations]
    exact actionMul_nativeCopiesSound place 297 input
  · refine actionNativeCopiesSound_after place _ _ ?_
    rw [FormalCircuit.call_regionCount]
    change 297 < 297 + 1
    decide

/-- All six original address-integrity regions preserve native-copy provenance. -/
theorem actionAddressIntegrity_nativeCopiesSound (place : RegionIndex → ℕ)
    (input : Var AddressIntegrity.Input Fp) :
    CircuitNativeCopiesSound place (actionNativeAdviceCopySource place)
      ((AddressIntegrity.circuit.call
        (actionConfig.eccConfig.mul, actionConfig.eccConfig.witnessPoint) input).operations 297) 297 := by
  rw [FormalCircuit.call_operations]
  simp only [AddressIntegrity.circuit, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, circuitNativeCopiesSound_append]
  constructor
  · exact actionMulCall_nativeCopiesSound place _
  · constructor
    · refine actionNativeCopiesSound_after place _ _ ?_
      rw [FormalCircuit.call_regionCount]
      change 297 < 297 + 4
      decide
    · refine actionNativeCopiesSound_after place _ _ ?_
      rw [FormalCircuit.call_regionCount, FormalCircuit.call_regionCount]
      change 297 < 297 + 4 + 1
      decide

/-- The original integrity-check stage reaches the annotated multiplier at exactly region 297. -/
theorem actionChecks_nativeCopiesSound (place : RegionIndex → ℕ)
    (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (witness : Circuit.Witnesses Fp) (cells : Circuit.WitnessCells) :
    CircuitNativeCopiesSound place (actionNativeAdviceCopySource place)
      ((Circuit.synthChecks generators bases witness actionConfig cells).operations 8) 8 := by
  rw [Circuit.synthChecks_eq]
  simp only [Circuit.synthChecksProgram, Circuit.loadPrivate, circuit_norm,
    circuitNativeCopiesSound_append, CircuitNativeCopiesSound, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, actionAddressIntegrity_nativeCopiesSound place _⟩
  all_goals try simp [RegionNativeCopiesSound]
  all_goals refine actionNativeCopiesSound_before place _ _ ?_
  all_goals first
    | (rw [Sinsemilla.Merkle.CalculateRoot.circuit_call_regionCount] <;> decide)
    | (rw [ValueCommit.circuit_call_regionCount] <;> decide)
    | (rw [DeriveNullifier.circuit_call_regionCount] <;> decide)
    | (rw [SpendAuthority.circuit_call_regionCount] <;> decide)
    | (rw [CommitIvk.Main.circuit_call_regionCount])

/-- The original witness, integrity, and note stages satisfy the native-source predicate in sequence. -/
theorem actionBase_nativeCopiesSound (place : RegionIndex → ℕ)
    (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (witness : Circuit.Witnesses Fp) :
    CircuitNativeCopiesSound place (actionNativeAdviceCopySource place)
      ((Circuit.synthesizeBase generators bases witness actionConfig).operations 0) 0 := by
  simp only [Circuit.synthesizeBase, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, circuitNativeCopiesSound_append, Circuit.synthWitness_nextRegionIndex,
    Circuit.synthChecks_nextRegionIndex, Circuit.synthWitness_regionCount,
    Circuit.synthChecks_regionCount, Nat.zero_add, Nat.reduceAdd]
  refine ⟨?_, actionChecks_nativeCopiesSound place generators bases witness _, ?_⟩
  · refine actionNativeCopiesSound_before place _ _ ?_
    rw [Circuit.synthWitness_regionCount]
    decide
  · exact actionNativeCopiesSound_after place _ 303 (by decide)

/-- Every native annotation describes the actual program in the complete opaque Action circuit. -/
theorem actionCircuit_nativeCopiesSound (place : RegionIndex → ℕ) :
    CircuitNativeCopiesSound place (actionNativeAdviceCopySource place) actionCircuit.operations 0 := by
  rw [Internal.actionCircuit_eq_impl]
  change CircuitNativeCopiesSound place (actionNativeAdviceCopySource place)
    ((Circuit.mainPost Specs.Sinsemilla.orchardGenerators orchardBases actionConfig ()).operations 0) 0
  simp only [Circuit.mainPost, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, circuitNativeCopiesSound_append]
  constructor
  · rw [FormalCircuit.call_operations]
    change CircuitNativeCopiesSound place (actionNativeAdviceCopySource place)
      ((Circuit.synthesizeBase Specs.Sinsemilla.orchardGenerators orchardBases
        Circuit.hintWitnesses actionConfig).operations 0) 0
    exact actionBase_nativeCopiesSound place _ _ _
  · refine actionNativeCopiesSound_after place _ _ ?_
    rw [FormalCircuit.call_regionCount]
    change 297 < 0 + 394
    decide

/-- All collected Action copy annotations have exact evaluator semantics, including native callbacks. -/
theorem actionAdviceAliasPrograms_sources :
    AdviceAliasSources actionCircuit.placement actionAdviceAliasPrograms := by
  exact circuitAdviceAliases_sources actionCircuit.placement
    (actionNativeAdviceCopySource actionCircuit.placement) actionCircuit.operations 0
    (actionCircuit_nativeCopiesSound actionCircuit.placement)

end Zcash.Snark.ZeroKnowledge
