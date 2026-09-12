import Zcash.Snark.ZeroKnowledge.ActionInstantiation
import Zcash.Snark.ZeroKnowledge.ActionGateValues
import Zcash.Snark.ZeroKnowledge.ActionLookupValues
import Zcash.Snark.ZeroKnowledge.ActionCopyValues
import Zcash.Snark.ZeroKnowledge.ActionRowRelations

/-!
# Source constraints establish the actual Action reference relation

This composition retains the finite gate and lookup activation checks explicitly.
Once those checks and the original operation constraints are available, it
constructs every row and copy premise required by the statistical ZK theorem.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common

/-- The actual generated Action rows satisfy the reference relation once the
original operation constraints and the finite activation scans have been checked. -/
theorem actionWitnessRows_relation_of_constraints {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (hgateCoverage : gateActivationCoverageCheck
      (actionCircuit.constraintSystem.gates.map sourceGateLabel)
      actionCircuit.selectorActivations
      (sourceGateActivationLabels actionCircuit.placement actionCircuit.operations 0) = true)
    (hlookupCoverage : lookupActivationCoverageCheck
      (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
      actionCircuit.selectorActivations
      (sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0) = true)
    (hconstraints : ∀ action : Fin actions, Constraints actionCircuit.placement
      (actionCircuit.environment (actionWitnessAssignment (inputs action) (witnesses action)))
      actionCircuit.operations 0) :
    ActionZkRelation urs hk inputs (actionWitnessRowBundle inputs witnesses) := by
  refine ⟨?_, ?_⟩
  · exact actionReferenceKey_rows_of_verifierCS urs hk actionCircuit_newFixedCols_eq_fifteen
      (actionPublicPolynomials inputs) (actionWitnessRowBundle inputs witnesses)
      (actionWitnessRows_gates_of_constraints inputs witnesses hgateCoverage hconstraints)
      (actionWitnessRows_lookups_of_constraints inputs witnesses hlookupCoverage hconstraints)
  · exact actionWitnessRows_copies_of_constraints inputs witnesses hconstraints _
      (actionReferenceKey_permutationChunks urs hk actionCircuit_newFixedCols_eq_fifteen)
      (actionReferenceKey_copyChunkWidths urs hk actionCircuit_newFixedCols_eq_fifteen)

end Zcash.Snark.ZeroKnowledge
