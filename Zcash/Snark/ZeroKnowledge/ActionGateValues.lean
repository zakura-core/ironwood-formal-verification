import Zcash.Snark.ZeroKnowledge.ActionQueryValuation
import Zcash.Snark.ZeroKnowledge.ActionSelectorMasking
import Zcash.Snark.ZeroKnowledge.ActionSourceMasking
import Zcash.Snark.ZeroKnowledge.InactiveGateCompleteness

/-!
# Gate equations of the actual generated Action rows
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Every compiled Action gate vanishes on the unused suffix, for arbitrary private advice. -/
theorem actionWitnessRows_inactiveGates {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (action : Fin actions) (row : Fin 2048) (hrow : 1779 ≤ row.val) :
    ∀ expression ∈ actionCircuit.verifierCS.gates,
      plonkExpressionRowValue (actionPublicPolynomials inputs)
        (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action row expression = 0 := by
  have hdomain : row.val < actionCircuit.n := by
    rw [TopLevelCircuit.n, actionCircuit_domainExponent_eq]
    exact row.isLt
  apply topLevel_verifierGates_zero_of_inactive actionCircuit
    (fun gate hgate constraint hconstraint =>
      List.all_eq_true.mp (List.all_eq_true.mp actionCircuit_sourceGateHomogeneous gate hgate)
        constraint hconstraint)
    row.val hdomain
    (actionResolvedQueryValuation
      (plonkFixedRowValues (actionPublicPolynomials inputs) row)
      (plonkAdviceRowValues (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action row)
      (plonkInstanceRowValues (actionPublicPolynomials inputs) action row))
  · intro selector; rfl
  · intro selector compressed hlookup
    have hbounds := actionCircuit_packedSelectorBounds actionCircuit_newFixedCols_eq_fifteen
      selector compressed hlookup
    exact actionResolvedQueryValuation_packed inputs row _ _ compressed.packedCol hbounds.1 hbounds.2
  · intro gate _
    exact actionCircuit_selector_inactive_after_placement gate.selector.index row.val hrow
  · exact actionResolvedQueryValuation_interprets _ _ _

/-- Source completeness and checked gate coverage imply every actual Action gate row. -/
theorem actionWitnessRows_gates_of_constraints {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (hcoverage : gateActivationCoverageCheck (actionCircuit.constraintSystem.gates.map sourceGateLabel)
      actionCircuit.selectorActivations
      (sourceGateActivationLabels actionCircuit.placement actionCircuit.operations 0) = true)
    (hconstraints : ∀ action : Fin actions, Constraints actionCircuit.placement
      (actionCircuit.environment (actionWitnessAssignment (inputs action) (witnesses action)))
      actionCircuit.operations 0) :
    ∀ action : Fin actions, ∀ row : Fin 2048, ∀ expression ∈ actionCircuit.verifierCS.gates,
      plonkExpressionRowValue (actionPublicPolynomials inputs)
        (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action row expression = 0 := by
  intro action row
  by_cases hlast : row.val < 2047
  · have hlabels : (actionCircuit.constraintSystem.gates.map sourceGateLabel).Nodup := by
      rw [Internal.actionCircuit_eq_impl]
      decide +kernel
    apply topLevel_verifierGates_zero_of_constraints actionCircuit
      (actionWitnessAssignment (inputs action) (witnesses action)) hlabels hcoverage (hconstraints action)
      (fun gate hgate constraint hconstraint =>
        List.all_eq_true.mp (List.all_eq_true.mp actionCircuit_sourceGateHomogeneous gate hgate)
          constraint hconstraint) row.val
    · rw [TopLevelCircuit.n, actionCircuit_domainExponent_eq]
      exact row.isLt
    · exact actionWitnessRowFeeds_interpret inputs witnesses action row hlast
  · exact actionWitnessRows_inactiveGates inputs witnesses action row (by omega)

end Zcash.Snark.ZeroKnowledge
