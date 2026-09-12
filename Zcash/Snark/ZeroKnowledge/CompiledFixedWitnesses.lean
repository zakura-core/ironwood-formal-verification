import Zcash.Snark.ZeroKnowledge.AdviceWitnessEquations
import Zcash.Snark.ZeroKnowledge.AdviceWitnessAssignment
import Zcash.Circuits.Integration.FixedLayout

/-!
# Compiler-owned fixed data satisfies the witness clauses

The source circuit's fixed-write and table clauses follow from its canonical
compiled fixed columns. Together with the advice read/write certificate, this
removes the fixed-environment premise from the witness interpreter's correctness
theorem. The read/write certificate itself is still a separate obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Erasing advice leaves exactly the region's fixed constraint family. -/
theorem erasedRegionWitnesses_iff_fixed {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (region : RegionIndex) (programs : RegionOperations F)
    (environment : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place region environment (eraseRegionAdvice programs) ↔
      CircuitConstraintFamily.regionConstraints .fixed place region environment.toEnvironment programs := by
  induction programs with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;>
      simp [eraseRegionAdvice, RegionOperations.ExtendsWitnesses, RegionOperation.ExtendsWitness,
        CircuitConstraintFamily.regionConstraints, CircuitConstraintFamily.regionConstraint,
        RegionOperation.Constraints, ih]

/-- Erasing advice leaves exactly the original circuit's fixed writes and table contents. -/
theorem erasedCircuitWitnesses_iff_fixed {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (programs : Operations F) (region : RegionIndex)
    (environment : ProverEnvironment F) :
    ExtendsWitnesses place environment (eraseCircuitAdvice programs) region ↔
      CircuitConstraintFamily.constraints .fixed place environment.toEnvironment programs region := by
  induction programs generalizing region with
  | nil => rfl
  | cons operation rest ih =>
    cases operation with
    | region name programs =>
      simp only [eraseCircuitAdvice, ExtendsWitnesses, CircuitConstraintFamily.constraints,
        erasedRegionWitnesses_iff_fixed, ih]
    | constrainInstance cell column row =>
      simpa [eraseCircuitAdvice, ExtendsWitnesses, CircuitConstraintFamily.constraints] using ih region
    | loadTable table values =>
      simp only [eraseCircuitAdvice, ExtendsWitnesses, CircuitConstraintFamily.constraints,
        ↓reduceIte, ih]
      tauto

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- A raw compiled fixed write is realized by the canonical cyclic field environment. -/
theorem compiledFixedValue_of_mem_raw (circuit : TopLevelCircuit Fp Config PublicInput)
    (entry : Layout.FixedAssignment Fp)
    (hentry : entry ∈ Layout.rawAssignments (circuit.usableRowsAt circuit.domainExponent)
      circuit.selectorMap circuit.constraintSystem circuit.operations) :
    circuit.fixedValue ⟨entry.1⟩ (entry.2.1 : ℤ) = entry.2.2 := by
  have hrow := (circuit.fixedAssignment_bounds_of_mem_raw entry hentry).2
  have hread := circuit.fixedRows_getD_getD_eq_of_mem_raw entry hentry
  change (circuit.fixedRows.getD entry.1 []).getD ((entry.2.1 : ℤ).natMod circuit.n) 0 = _
  have hmod : (entry.2.1 : ℤ).natMod circuit.n = entry.2.1 := by
    simp only [Int.natMod]
    exact Nat.mod_eq_of_lt hrow
  rw [hmod]
  exact hread

/-- Canonical compiled fixed columns discharge the whole original fixed constraint family. -/
theorem compiledEnvironment_fixedConstraints (circuit : TopLevelCircuit Fp Config PublicInput)
    (assignment : ProofAssignment Fp) :
    CircuitConstraintFamily.constraints .fixed circuit.placement
      (circuit.environment assignment) circuit.operations 0 := by
  apply FixedLayout.constraints_of_entries circuit.regionStarts
    (circuit.usableRowsAt circuit.domainExponent) circuit.operations 0
    (circuit.environment assignment) rfl
  intro column row value hentry
  rw [TopLevelCircuit.environment_fixed]
  apply compiledFixedValue_of_mem_raw circuit (column, row, value)
  rcases List.mem_append.mp hentry with htable | hregion
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ htable))
  · exact List.mem_append_right _ hregion

/-- The compiler supplies every advice-erased witness clause, independently of advice and hints. -/
theorem compiledEnvironment_fixedWitnesses (circuit : TopLevelCircuit Fp Config PublicInput)
    (assignment : ProofAssignment Fp) (hints : ProverHint Fp) :
    ExtendsWitnesses circuit.placement (circuit.proverEnvironment assignment hints)
      (eraseCircuitAdvice circuit.operations) 0 := by
  apply (erasedCircuitWitnesses_iff_fixed circuit.placement circuit.operations 0 _).mpr
  exact compiledEnvironment_fixedConstraints circuit assignment

/-- Causal, distinct advice writes suffice for witness extension in the exact compiled environment. -/
theorem topLevelAdviceAssignment_extendsWitnesses (circuit : TopLevelCircuit Fp Config PublicInput)
    (initial : ProofAssignment Fp) (hints : ProverHint Fp)
    (hcausal : AdviceProgramsCausal circuit.placement []
      (circuitAdvicePrograms circuit.placement circuit.operations 0))
    (hnodup : ((circuitAdvicePrograms circuit.placement circuit.operations 0).map adviceProgramTarget).Nodup) :
    ExtendsWitnesses circuit.placement
      (circuit.proverEnvironment (topLevelAdviceAssignment circuit initial hints) hints)
      circuit.operations 0 := by
  rw [topLevelAdviceAssignment_environment]
  exact runCircuitAdvice_extendsWitnesses circuit.placement circuit.operations 0
    (circuit.proverEnvironment initial hints) hcausal hnodup
    (compiledEnvironment_fixedWitnesses circuit initial hints)

end Zcash.Snark.ZeroKnowledge
