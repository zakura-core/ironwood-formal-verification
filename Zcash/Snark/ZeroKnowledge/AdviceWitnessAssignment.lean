import Zcash.Snark.ZeroKnowledge.AdviceWitnessExecution
import Clean.Halo2.TopLevel

/-!
# From witness execution to a compiler-owned assignment

The interpreter starts with the circuit's fixed columns, its declared public
input layout, zero advice, and a supplied hint store. Rebuilding the canonical
compiler environment from its final advice produces exactly the environment
used by the interpreter. Gate and lookup satisfaction is a separate obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Fieldwise extensionality of the complete prover environment. -/
theorem proverEnvironment_ext {F : Type} {left right : ProverEnvironment F}
    (hget : left.get = right.get) (hrows : left.usableRows = right.usableRows)
    (hhint : left.hint = right.hint) : left = right := by
  rcases left with ⟨⟨leftGet, leftRows⟩, leftHint⟩
  rcases right with ⟨⟨rightGet, rightRows⟩, rightHint⟩
  cases hget
  cases hrows
  cases hhint
  rfl

variable {F : Type} [FiniteField F] {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- Initialize zero advice and serialize the exact circuit-owned public-input layout. -/
def initialPublicWitnessAssignment (circuit : TopLevelCircuit F Config PublicInput)
    (inputs : PublicInput F) : ProofAssignment F := {
  advice := fun _ _ => 0
  inst := fun column row =>
    if 0 ≤ row then (circuit.publicInputRows inputs column).getD row.toNat 0 else 0
}

/-- Every nonnegative instance read is the corresponding serialized public row. -/
theorem initialPublicWitnessAssignment_inst (circuit : TopLevelCircuit F Config PublicInput)
    (inputs : PublicInput F) (column : Column .instance) (row : ℕ) :
    (initialPublicWitnessAssignment circuit inputs).inst column (row : ℤ) =
      (circuit.publicInputRows inputs column).getD row 0 := by
  simp only [initialPublicWitnessAssignment, Nat.cast_nonneg, if_true, Int.toNat_natCast]

/-- The initial canonical environment extracts exactly the supplied public input. -/
theorem initialPublicWitnessAssignment_publicInput (circuit : TopLevelCircuit F Config PublicInput)
    (inputs : PublicInput F) :
    circuit.publicInputLayout.extract (circuit.environment (initialPublicWitnessAssignment circuit inputs)) = inputs := by
  apply PublicInputLayout.extract_eq
  intro index
  rw [TopLevelCircuit.environment_inst, initialPublicWitnessAssignment_inst]
  exact circuit.publicInputRows_getD_cell inputs index

/-- Execute every original advice program using the circuit's own placement and fixed environment. -/
def topLevelAdviceEnvironment (circuit : TopLevelCircuit F Config PublicInput)
    (initial : ProofAssignment F) (hints : ProverHint F) : ProverEnvironment F :=
  runAdvicePrograms circuit.placement (circuitAdvicePrograms circuit.placement circuit.operations 0)
    (circuit.proverEnvironment initial hints)

/-- Retain the executed advice as proof assignment data, with exactly the original public inputs. -/
def topLevelAdviceAssignment (circuit : TopLevelCircuit F Config PublicInput)
    (initial : ProofAssignment F) (hints : ProverHint F) : ProofAssignment F := {
  advice := (topLevelAdviceEnvironment circuit initial hints).advice
  inst := initial.inst
}

/-- Reconstructing the compiler's environment from the executed advice changes no cell or metadata. -/
theorem topLevelAdviceAssignment_environment (circuit : TopLevelCircuit F Config PublicInput)
    (initial : ProofAssignment F) (hints : ProverHint F) :
    circuit.proverEnvironment (topLevelAdviceAssignment circuit initial hints) hints =
      topLevelAdviceEnvironment circuit initial hints := by
  apply proverEnvironment_ext
  · funext column row
    rcases column with ⟨kind, index⟩
    cases kind with
    | advice => rfl
    | fixed =>
      exact (runAdvicePrograms_get_nonadvice circuit.placement _
        (circuit.proverEnvironment initial hints) ⟨.fixed, index⟩ row (by simp)).symm
    | «instance» =>
      exact (runAdvicePrograms_get_nonadvice circuit.placement _
        (circuit.proverEnvironment initial hints) ⟨.instance, index⟩ row (by simp)).symm
  · exact (runAdvicePrograms_usableRows circuit.placement _
      (circuit.proverEnvironment initial hints)).symm
  · exact (runAdvicePrograms_hint circuit.placement _
      (circuit.proverEnvironment initial hints)).symm

/-- Executing advice preserves the extracted public statement under the same canonical layout. -/
theorem topLevelAdviceAssignment_publicInput (circuit : TopLevelCircuit F Config PublicInput)
    (initial : ProofAssignment F) (hints : ProverHint F) :
    circuit.publicInputLayout.extract (circuit.environment (topLevelAdviceAssignment circuit initial hints)) =
      circuit.publicInputLayout.extract (circuit.environment initial) := by
  rfl

/-- Starting from an application's public data and running its hints preserves that exact data. -/
theorem generatedAdviceAssignment_publicInput (circuit : TopLevelCircuit F Config PublicInput)
    (inputs : PublicInput F) (hints : ProverHint F) :
    circuit.publicInputLayout.extract (circuit.environment
      (topLevelAdviceAssignment circuit (initialPublicWitnessAssignment circuit inputs) hints)) = inputs := by
  rw [topLevelAdviceAssignment_publicInput, initialPublicWitnessAssignment_publicInput]

end Zcash.Snark.ZeroKnowledge
