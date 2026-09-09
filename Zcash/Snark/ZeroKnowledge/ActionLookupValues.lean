import Zcash.Snark.ZeroKnowledge.ActionLookupFallback
import Zcash.Snark.ZeroKnowledge.ActionQueryRows
import Zcash.Snark.ZeroKnowledge.LookupActivationCoverage
import Zcash.Circuits.Action.Planner

/-!
# All usable Action lookup tuples in the prover's actual query feeds

Active rows use their original lookup constraint and the exact compressed
selector values. Inactive rows select the proved zero-index table entry.
The final result retains the actual input/table pairing through query erasure.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 10000

/-- Every inactive Action lookup chooses the corresponding actual zero-index table entry. -/
theorem actionLookup_inactive_input (assignment : ProofAssignment Fp)
    (argument : LookupArgument Fp) (hargument : argument ∈ actionCircuit.constraintSystem.lookups)
    (valuation : Query → Fp) (hinactive : valuation (.selector argument.masterSelector) = 0) :
    argument.inputs.map (Expression.eval valuation) =
      argument.tables.map (Expression.eval
        (Query.eval (actionCircuit.environment assignment) (fun _ => 0) 0)) := by
  have htable := actionCircuit_generatorTable_zero assignment
  rw [actionCircuit_lookupArguments_eq] at hargument
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hargument
  rcases hargument with rfl | rfl | rfl
  · rw [rangeCheckLookup_inactive 10 _ valuation hinactive]
    change [0] = [(actionCircuit.environment assignment).fixed
      actionConfig.sinsemilla1.generatorTable.tableIdx.inner 0]
    rw [htable.1]
  · rw [sinsemillaLookup_inactive _ _ valuation hinactive]
    change [0, (Specs.Sinsemilla.orchardGenerators.S 0).x, (Specs.Sinsemilla.orchardGenerators.S 0).y] =
      [(actionCircuit.environment assignment).fixed actionConfig.sinsemilla1.generatorTable.tableIdx.inner 0,
        (actionCircuit.environment assignment).fixed actionConfig.sinsemilla1.generatorTable.tableX.inner 0,
        (actionCircuit.environment assignment).fixed actionConfig.sinsemilla1.generatorTable.tableY.inner 0]
    rw [htable.1, htable.2.1, htable.2.2]
  · rw [sinsemillaLookup_inactive _ _ valuation hinactive]
    change [0, (Specs.Sinsemilla.orchardGenerators.S 0).x, (Specs.Sinsemilla.orchardGenerators.S 0).y] =
      [(actionCircuit.environment assignment).fixed actionConfig.sinsemilla1.generatorTable.tableIdx.inner 0,
        (actionCircuit.environment assignment).fixed actionConfig.sinsemilla1.generatorTable.tableX.inner 0,
        (actionCircuit.environment assignment).fixed actionConfig.sinsemilla1.generatorTable.tableY.inner 0]
    rw [htable.1, htable.2.1, htable.2.2]

/-- Original Action constraints imply every uncompressed source lookup tuple, including inactive rows. -/
theorem actionLookup_tuple_of_constraints (assignment : ProofAssignment Fp)
    (hcoverage : lookupActivationCoverageCheck
      (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
      actionCircuit.selectorActivations
      (sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0) = true)
    (hconstraints : Constraints actionCircuit.placement (actionCircuit.environment assignment)
      actionCircuit.operations 0)
    (argument : LookupArgument Fp) (hargument : argument ∈ actionCircuit.constraintSystem.lookups)
    (row : Fin 2042) :
    ∃ target : Fin 2042,
      argument.inputs.map (Expression.eval (substValuation actionCircuit.selectorMap.lookup
        (Query.eval (actionCircuit.environment assignment) (fun _ => 0) row.val))) =
      argument.tables.map (Expression.eval (substValuation actionCircuit.selectorMap.lookup
        (Query.eval (actionCircuit.environment assignment) (fun _ => 0) target.val))) := by
  have husable : actionCircuit.usableRowsAt actionCircuit.domainExponent = 2042 := by
    rw [TopLevelCircuit.usableRowsAt, actionCircuit_domainExponent_eq, actionCircuit_blindingFactors_eq]
    decide
  have hdomain : row.val < actionCircuit.n := by
    rw [TopLevelCircuit.n, actionCircuit_domainExponent_eq]
    exact row.isLt.trans (by decide : 2042 < 2048)
  by_cases hactive : (argument.masterSelector.index, row.val) ∈ actionCircuit.selectorActivations
  · have hmasters :
        (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index)).Nodup := by
      rw [Internal.actionCircuit_eq_impl]
      decide +kernel
    obtain ⟨lookup, hlookup, hargumentEq, hrow⟩ := topLevel_lookup_enabled_of_coverage
      actionCircuit hmasters hcoverage argument hargument row.val hactive
    obtain ⟨target, htarget, hequal⟩ := topLevel_enabledLookup_tuple_of_constraints actionCircuit
      assignment (selectorAnchor actionConfig) actionCircuit_lookupSelectorAnchorRequirements_satisfied
      hconstraints lookup hlookup
    have ht : target < 2042 := by simpa only [husable] using htarget
    refine ⟨⟨target, ht⟩, ?_⟩
    simpa only [hargumentEq, ← Nat.cast_add, hrow] using hequal
  · refine ⟨0, ?_⟩
    have hzero : (substValuation actionCircuit.selectorMap.lookup
        (Query.eval (actionCircuit.environment assignment) (fun _ => 0) row.val))
        (.selector argument.masterSelector) = 0 := by
      cases hlookup : actionCircuit.selectorMap.lookup argument.masterSelector.index with
      | none => simp [substValuation, hlookup, Query.eval]
      | some compressed =>
        simp only [substValuation, ComplexSelector.toSelector, hlookup]
        apply topLevel_selReplacement_zero_of_inactive actionCircuit argument.masterSelector.index
          compressed hlookup row.val hdomain _ ?_ hactive
        simpa only [Query.eval, add_zero] using topLevel_environment_fixed_nat actionCircuit
          assignment ⟨compressed.packedCol⟩ row.val hdomain
    have hfallback := actionLookup_inactive_input assignment argument hargument _ hzero
    refine hfallback.trans ?_
    symm
    apply List.map_congr_left
    intro expression hexpression
    exact Expression.eval_substValuation_eq_queryEval_of_selectorFree actionCircuit.selectorMap
      (actionCircuit.environment assignment) (fun _ => 0) 0 expression (argument.tablesFree expression hexpression)

/-- All original Action lookup tuples survive the exact verifier query compiler. -/
theorem actionWitnessRows_lookups_of_constraints {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (witnesses : Fin actions → PrivateWitness)
    (hcoverage : lookupActivationCoverageCheck
      (actionCircuit.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
      actionCircuit.selectorActivations
      (sourceLookupActivationLabels actionCircuit.placement actionCircuit.operations 0) = true)
    (hconstraints : ∀ action : Fin actions, Constraints actionCircuit.placement
      (actionCircuit.environment (actionWitnessAssignment (inputs action) (witnesses action)))
      actionCircuit.operations 0) :
    ∀ action : Fin actions, ∀ lookup : Fin actionCircuit.lookupCount, ∀ row : Fin 2042,
      ∃ target : Fin 2042,
        (actionCircuit.verifierCS.lookupInputExprs lookup).map
          (plonkExpressionRowValue (actionPublicPolynomials inputs)
            (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action (row.castLE (by decide))) =
        (actionCircuit.verifierCS.lookupTableExprs lookup).map
          (plonkExpressionRowValue (actionPublicPolynomials inputs)
            (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action (target.castLE (by decide))) := by
  intro action lookup row
  obtain ⟨target, htarget⟩ := actionLookup_tuple_of_constraints
    (actionWitnessAssignment (inputs action) (witnesses action)) hcoverage (hconstraints action)
    actionCircuit.constraintSystem.lookups[lookup.val] (List.getElem_mem lookup.isLt) row
  have project (atRow : Fin 2042) := topLevel_verifierLookup_eval actionCircuit
    (plonkFixedRowValues (actionPublicPolynomials inputs) (atRow.castLE (by decide)))
    (plonkAdviceRowValues (plonkUnmaskedAdviceRows (actionWitnessRowBundle inputs witnesses)) action
      (atRow.castLE (by decide)))
    (plonkInstanceRowValues (actionPublicPolynomials inputs) action (atRow.castLE (by decide)))
    _ lookup (actionWitnessRowFeeds_interpret inputs witnesses action (atRow.castLE (by decide))
      (atRow.isLt.trans (by decide : 2042 < 2047)))
  exact ⟨target, (project row).1.trans (htarget.trans (project target).2.symm)⟩

end Zcash.Snark.ZeroKnowledge
