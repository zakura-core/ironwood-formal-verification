import Zcash.Snark.ZeroKnowledge.ActionDerivedKey
import Zcash.Snark.ZeroKnowledge.KeygenExpressionDegree
import Zcash.Snark.ZeroKnowledge.PlonkDegree

/-!
# Action expression degrees from configuration

The source degree vectors are reduced directly from Action's configure program.
The general compiler lemmas transport the lookup bounds through singleton selector
substitution and query resolution. The permutation widths come from the actual
compiler key. Only the compiled custom-gate degree bound remains in the final
profile constructor.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

/-- The source degrees used by Action's selector compressor, in selector-allocation order. -/
def actionSelectorDegrees : Array ℕ :=
  #[3, 2, 0, 0, 3, 5, 4, 4, 6, 4, 4, 4, 4, 4, 4, 3, 5, 3, 9, 9, 3, 5, 6, 6, 2, 0,
    4, 3, 2, 0, 4, 3, 2, 3, 3, 3, 2, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 2, 3, 3, 3]

set_option maxRecDepth 10000 in
/-- The fifty-six selector degrees are exactly those computed from the Action source gates. -/
theorem actionCircuit_selectorMaxDegrees :
    selectorMaxDegrees actionCircuit.constraintSystem = actionSelectorDegrees := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

set_option maxRecDepth 10000 in
/-- Exact source degrees of the three Action lookup input tuples. -/
theorem actionCircuit_lookupInputDegrees :
    actionCircuit.constraintSystem.lookups.map
      (fun lookup => lookup.inputs.map Expression.degree) = [[3], [4, 2, 4], [4, 2, 4]] := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

set_option maxRecDepth 10000 in
/-- Every Action lookup-table expression has degree one. -/
theorem actionCircuit_lookupTableDegrees :
    actionCircuit.constraintSystem.lookups.map
      (fun lookup => lookup.tables.map Expression.degree) = [[1], [1, 1, 1], [1, 1, 1]] := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- Every Action source lookup input has degree at most four. -/
theorem actionCircuit_lookupInput_degree_le (argument : LookupArgument Fp)
    (hargument : argument ∈ actionCircuit.constraintSystem.lookups)
    (expression : Expression Fp Query) (hexpression : expression ∈ argument.inputs) :
    expression.degree ≤ 4 := by
  have hdegree : expression.degree ∈ (actionCircuit.constraintSystem.lookups.map
      (fun lookup => lookup.inputs.map Expression.degree)).flatten :=
    List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨argument, hargument, rfl⟩,
      List.mem_map.mpr ⟨expression, hexpression, rfl⟩⟩
  rw [actionCircuit_lookupInputDegrees] at hdegree
  simp only [List.flatten_cons, List.flatten_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hdegree
  omega

/-- Every Action source lookup-table expression has degree at most one. -/
theorem actionCircuit_lookupTable_degree_le (argument : LookupArgument Fp)
    (hargument : argument ∈ actionCircuit.constraintSystem.lookups)
    (expression : Expression Fp Query) (hexpression : expression ∈ argument.tables) :
    expression.degree ≤ 1 := by
  have hdegree : expression.degree ∈ (actionCircuit.constraintSystem.lookups.map
      (fun lookup => lookup.tables.map Expression.degree)).flatten :=
    List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨argument, hargument, rfl⟩,
      List.mem_map.mpr ⟨expression, hexpression, rfl⟩⟩
  rw [actionCircuit_lookupTableDegrees] at hdegree
  simp only [List.flatten_cons, List.flatten_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hdegree
  omega

/-- Singleton selector compression preserves the Action lookup-input bound in the actual verifier CS. -/
theorem actionCircuit_verifierLookupInput_degree_le (lookup : Fin actionCircuit.lookupCount)
    (expression : Expr Fp) (hexpression : expression ∈ actionCircuit.verifierCS.lookupInputExprs lookup) :
    expression.degreeBound ≤ 4 :=
  topLevel_lookupInput_degree_le actionCircuit 4 actionCircuit_lookupInput_degree_le lookup expression hexpression

/-- The actual compiled Action lookup-table expressions retain degree at most one. -/
theorem actionCircuit_verifierLookupTable_degree_le (lookup : Fin actionCircuit.lookupCount)
    (expression : Expr Fp) (hexpression : expression ∈ actionCircuit.verifierCS.lookupTableExprs lookup) :
    expression.degreeBound ≤ 1 :=
  topLevel_lookupTable_degree_le actionCircuit 1 actionCircuit_lookupTable_degree_le lookup expression hexpression

private theorem castKey_lookupDegrees {G : Type} {source target : CircuitShape}
    (hshape : source = target) (key : VerifyingKey source Fp G) (inputBound tableBound : ℕ)
    (hinputs : ∀ lookup expression, expression ∈ key.lookupInputExprs lookup → expression.degreeBound ≤ inputBound)
    (htables : ∀ lookup expression, expression ∈ key.lookupTableExprs lookup → expression.degreeBound ≤ tableBound) :
    (∀ lookup expression, expression ∈ (hshape ▸ key).lookupInputExprs lookup → expression.degreeBound ≤ inputBound) ∧
      (∀ lookup expression, expression ∈ (hshape ▸ key).lookupTableExprs lookup → expression.degreeBound ≤ tableBound) := by
  cases hshape
  exact ⟨hinputs, htables⟩

/-- Both lookup degree bounds hold for the compiler-derived Action reference key. -/
theorem actionReferenceKey_lookupDegrees {G : Type} [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11) (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    (∀ lookup expression,
      expression ∈ (actionReferenceKey (actions := actions) urs hk hpacked).lookupInputExprs lookup →
        expression.degreeBound ≤ 4) ∧
      (∀ lookup expression,
        expression ∈ (actionReferenceKey (actions := actions) urs hk hpacked).lookupTableExprs lookup →
          expression.degreeBound ≤ 1) :=
  castKey_lookupDegrees _ _ 4 1 actionCircuit_verifierLookupInput_degree_le
    actionCircuit_verifierLookupTable_degree_le

/-- Only custom-gate degrees remain after configuration and compilation supply the other three profile fields. -/
theorem actionReferenceKey_degreeProfile_of_gates {G : Type} [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11) (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (hgates : ∀ expression ∈ (actionReferenceKey (actions := actions) urs hk hpacked).gates,
      expression.degreeBound ≤ 9) :
    PlonkDegreeProfile (actions := actions) (actionReferenceKey urs hk hpacked) := by
  have hlookup := actionReferenceKey_lookupDegrees (actions := actions) urs hk hpacked
  refine ⟨hgates, ?_, hlookup.1, hlookup.2⟩
  rw [actionReferenceKey_permutationChunks]
  decide +kernel

end Zcash.Snark.ZeroKnowledge
