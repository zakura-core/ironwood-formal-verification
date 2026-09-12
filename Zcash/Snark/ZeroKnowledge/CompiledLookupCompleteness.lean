import Zcash.Snark.ZeroKnowledge.CompiledGateCompleteness
import Zcash.Circuits.Integration.LookupSelectorRows

/-!
# Original lookup constraints in the actual compiler environment

The compiler's exact dense selector values reproduce the operation-local lookup
modes. Query erasure then preserves both input and table tuples. This connection
uses original constraints and selector placement, independently of proof emission.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- The actual compiler environment realizes every selector leaf of an enabled lookup. -/
theorem topLevel_enabledLookup_selectorProjection
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied top.lookupSelectorAnchorRequirements anchor)
    (lookup : EnabledLookup Fp) (henabled : lookup ∈ operationEnabledLookups top.operations 0) :
    lookup.SelectorProjection top (top.environment assignment) := by
  apply EnabledLookup.SelectorProjection.ofInputSelectorValues _ lookup ?_
    (lookupTables_selectorFree lookup.argument)
  intro expression hexpression
  apply expression_eval_substValuation_eq_queryEval_of_selectorLeaves
  have hexact := EnabledLookup.inputSelectorLeafRowsExact top anchor hanchor lookup henabled
  have hleaves := List.forall_iff_forall_mem.mp hexact expression hexpression
  apply hleaves.mono
  intro selector hvalue
  cases hlookup : top.selectorMap.lookup selector.index with
  | none =>
    simp only [hlookup] at hvalue
    simpa only [substValuation, hlookup, Query.eval] using hvalue.symm
  | some compressed =>
    simp only [hlookup] at hvalue
    simp only [substValuation, hlookup]
    rw [← hvalue.2, selReplacement_eval, selReplacement_eval]
    simp only [Query.eval, add_zero, ← Nat.cast_add]
    rw [topLevel_environment_fixed_nat top assignment ⟨compressed.packedCol⟩ _
      ((lookup.activationRow_lt_usableRows henabled).trans_le top.usableRowsAt_domainExponent_le_n)]

/-- Arbitrary interpreted query feeds retain both original selector-substituted lookup tuples. -/
theorem topLevel_verifierLookup_eval
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (fixed advice instanceFeed : ℕ → Fp) (valuation : Query → Fp)
    (lookup : Fin top.lookupCount)
    (hinterprets : Interprets top.gateQueryState fixed advice instanceFeed valuation) :
    ((top.verifierCS.lookupInputExprs lookup).map (Expr.eval fixed advice instanceFeed) =
      top.constraintSystem.lookups[lookup.val].inputs.map
        (Expression.eval (substValuation top.selectorMap.lookup valuation))) ∧
    ((top.verifierCS.lookupTableExprs lookup).map (Expr.eval fixed advice instanceFeed) =
      top.constraintSystem.lookups[lookup.val].tables.map
        (Expression.eval (substValuation top.selectorMap.lookup valuation))) := by
  have hargument := List.getElem_mem lookup.isLt
  have hpinned : Interprets (pinnedQueryState top.pinnedCS) fixed advice instanceFeed valuation := by
    rw [top.pinnedQueryState_eq_gateQueryState]
    exact hinterprets
  have hproject := top.lookup_eval fixed advice instanceFeed valuation lookup
    (topLevelLookupInputs_selectorsCovered top _ hargument)
    (TopLevelLookup.tablesCovered (top := top) _)
    hpinned
  constructor
  · rw [top.verifierCS_lookupInputExprs, map_eval_toExpr]
    exact hproject.1
  · rw [top.verifierCS_lookupTableExprs, map_eval_toExpr]
    exact hproject.2

/-- An enabled original lookup supplies its unchanged tuple membership after selector compilation. -/
theorem topLevel_enabledLookup_tuple_of_constraints
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (anchor : ℕ → FloorPlanner.RegionColumn)
    (hanchor : SelectorAnchorRequirementsSatisfied top.lookupSelectorAnchorRequirements anchor)
    (hconstraints : Constraints top.placement (top.environment assignment) top.operations 0)
    (lookup : EnabledLookup Fp) (henabled : lookup ∈ operationEnabledLookups top.operations 0) :
    ∃ target, target < top.usableRowsAt top.domainExponent ∧
      lookup.argument.inputs.map (Expression.eval (substValuation top.selectorMap.lookup
        (Query.eval (top.environment assignment) (fun _ => 0)
          (top.placement lookup.region + lookup.row)))) =
      lookup.argument.tables.map (Expression.eval (substValuation top.selectorMap.lookup
        (Query.eval (top.environment assignment) (fun _ => 0) target))) := by
  have hsatisfied := (CircuitConstraintFamily.lookup_constraints_iff_enabledLookups top.placement
    (top.environment assignment) top.operations 0).mp (FullCircuitSatisfaction.of_constraints hconstraints).lookups
  obtain ⟨target, htarget, hequal⟩ := List.forall_iff_forall_mem.mp hsatisfied lookup henabled
  have projection := topLevel_enabledLookup_selectorProjection top assignment anchor hanchor lookup henabled
  refine ⟨target, htarget, ?_⟩
  rw [projection.input, projection.table target htarget]
  exact hequal

end Zcash.Snark.ZeroKnowledge
