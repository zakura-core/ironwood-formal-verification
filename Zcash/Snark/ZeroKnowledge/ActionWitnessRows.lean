import Zcash.Snark.ZeroKnowledge.AdviceWitnessAssignment
import Zcash.Snark.ZeroKnowledge.ActionWitnessHintWindows
import Zcash.Circuits.Action.TopLevel

/-!
# Constructing the original Action advice rows

This constructor runs the actual fixed `actionCircuit.operations` at the
circuit-owned V1 placement. It initializes the declared public-input rows and
compiled fixed columns, installs the application witness hints, and retains the
resulting ten advice columns on the 2048-row domain.

The definition and public-input preservation do not yet establish that the final
assignment extends every witness program or satisfies the circuit constraints.
Those claims require the remaining read-dependency, extraction, and completeness
proofs; no successful proof attempt or verifier acceptance is assumed here.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2
open Zcash.Circuits
open Zcash.Circuits.Action

/-- Execute the actual Action witness programs and retain the resulting original assignment. -/
def actionWitnessAssignment (inputs : PublicInputs Fp) (witness : PrivateWitness) : ProofAssignment Fp :=
  topLevelAdviceAssignment actionCircuit (initialPublicWitnessAssignment actionCircuit inputs)
    (actionWitnessHints witness)

/-- The ten original advice columns supplied to the existing 2048-row reference prover. -/
def actionWitnessRows (inputs : PublicInputs Fp) (witness : PrivateWitness) : Fin 10 → Fin 2048 → Fp :=
  fun column row => (actionWitnessAssignment inputs witness).advice ⟨column.val⟩ (row.val : ℤ)

/-- Bundle the independently constructed Action assignments in the reference prover's witness shape. -/
def actionWitnessRowBundle {actions : ℕ} (inputs : Fin actions → PublicInputs Fp)
    (witnesses : Fin actions → PrivateWitness) : Fin actions → Fin 10 → Fin 2048 → Fp :=
  fun action => actionWitnessRows (inputs action) (witnesses action)

/-- The compiler environment reconstructed from the generated advice is exactly its execution environment. -/
theorem actionWitnessAssignment_environment (inputs : PublicInputs Fp) (witness : PrivateWitness) :
    actionCircuit.proverEnvironment (actionWitnessAssignment inputs witness) (actionWitnessHints witness) =
      topLevelAdviceEnvironment actionCircuit (initialPublicWitnessAssignment actionCircuit inputs)
        (actionWitnessHints witness) :=
  topLevelAdviceAssignment_environment actionCircuit _ _

/-- The generated assignment preserves the exact declared public Action statement. -/
theorem actionWitnessAssignment_publicInput (inputs : PublicInputs Fp) (witness : PrivateWitness) :
    actionCircuit.publicInputLayout.extract (actionCircuit.environment (actionWitnessAssignment inputs witness)) = inputs :=
  generatedAdviceAssignment_publicInput actionCircuit inputs (actionWitnessHints witness)

/-- Decoding the fixed program in the actual constructed environment gives the original application data. -/
theorem actionWitnessAssignment_hintData (inputs : PublicInputs Fp) (witness : PrivateWitness)
    (bounds : ActionScalarHintBounds witness) :
    @Eval.eval _ _ _ (CircuitType.proverEval Circuit.PrivateInputs)
      (actionCircuit.placedProverEnvironment (actionWitnessAssignment inputs witness) (actionWitnessHints witness))
      Circuit.hintWitnesses = actionWitnessHintData witness :=
  actionWitnessHints_decode witness bounds actionCircuit.placement
    (actionCircuit.environment (actionWitnessAssignment inputs witness))

/-- The same actual environment supplies canonical scalar windows to all five fixed-base gadgets. -/
theorem actionWitnessAssignment_hintWindows (inputs : PublicInputs Fp) (witness : PrivateWitness)
    (bounds : ActionScalarHintBounds witness) :
    let penv := actionCircuit.placedProverEnvironment (actionWitnessAssignment inputs witness) (actionWitnessHints witness)
    actionScalarWindowValues Circuit.hintWitnesses.rcv penv = canonicalActionScalarWindows witness.rcv.2 ∧
    actionScalarWindowValues Circuit.hintWitnesses.alpha penv = canonicalActionScalarWindows witness.alpha.2 ∧
    actionScalarWindowValues Circuit.hintWitnesses.rivk penv = canonicalActionScalarWindows witness.rivk.2 ∧
    actionScalarWindowValues Circuit.hintWitnesses.rcmOld penv = canonicalActionScalarWindows witness.rcmOld.2 ∧
    actionScalarWindowValues Circuit.hintWitnesses.rcmNew penv = canonicalActionScalarWindows witness.rcmNew.2 :=
  actionWitnessHintWindows_canonical witness bounds actionCircuit.placement
    (actionCircuit.environment (actionWitnessAssignment inputs witness))

end Zcash.Snark.ZeroKnowledge
