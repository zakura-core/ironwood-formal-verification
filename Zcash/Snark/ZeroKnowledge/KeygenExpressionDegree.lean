import Clean.Halo2.TopLevel
import Zcash.Circuits.Integration.VerifierCS
import Zcash.Snark.Soundness.Pricing.DegreeWalk

/-!
# Degree bounds through the expression compiler

Resolving query indices and translating the expression syntax do not increase
degree. Lookup selectors compile to singleton fixed queries, so their substitution
preserves the source degree. Lookup tables are selector-free already.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Query resolution and translation to the verifier syntax never increase the expression degree. -/
theorem eraseExpr_toExpr_degree_le {F : Type} [Field F] [DecidableEq F]
    (expression : Expression F Query) (queries : QueryState) :
    (RichExpression.toExpr (eraseExpr expression queries)).degreeBound ≤ expression.degree := by
  fun_induction eraseExpr expression queries <;>
    simp_all [eraseExpr, RichExpression.toExpr, Expr.degreeBound, Expression.degree] <;> omega

/-- Replacing every selector by a singleton packed query preserves the syntactic degree. -/
theorem substSelectorMap_degree_singleton {F : Type} [Field F]
    (map : ℕ → Option SelCompress) (expression : Expression F Query)
    (hmap : ∀ selector ∈ expression.selectorIndices, ∃ compressed,
      map selector = some compressed ∧ compressed.combinationLen = 1 ∧ compressed.assignedRoot = 1) :
    (substSelectorMap map expression).degree = expression.degree := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          obtain ⟨compressed, hlookup, hlength, hroot⟩ :=
            hmap selector.index (by simp [Expression.selectorIndices])
          simp [substSelectorMap, hlookup, selReplacement, hlength, hroot, Expression.degree]
      | fixed | advice | «instance» => rfl
  | const => rfl
  | add left right ihl ihr =>
      simp only [Expression.selectorIndices, List.mem_append] at hmap
      simp only [substSelectorMap, Expression.degree,
        ihl (fun s hs => hmap s (Or.inl hs)), ihr (fun s hs => hmap s (Or.inr hs))]
  | mul left right ihl ihr =>
      simp only [Expression.selectorIndices, List.mem_append] at hmap
      simp only [substSelectorMap, Expression.degree,
        ihl (fun s hs => hmap s (Or.inl hs)), ihr (fun s hs => hmap s (Or.inr hs))]

variable {F : Type} [FiniteField F]
variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- A bound after selector substitution survives the complete custom-gate compiler. -/
theorem topLevel_gate_degree_le (top : TopLevelCircuit F Config PublicInput) (bound : ℕ)
    (hsource : ∀ expression ∈ flatGates top.constraintSystem,
      (substSelectorMap top.selectorMap.lookup expression).degree ≤ bound)
    (expression : Expr F) (hexpression : expression ∈ top.verifierCS.gates) :
    expression.degreeBound ≤ bound := by
  simp only [TopLevelCircuit.verifierCS_gates, TopLevelCircuit.pinnedCS,
    PinnedConstraintSystem.derive, projectCS, eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsourceMem, rfl⟩ := List.mem_map.mp hexpression
  exact (eraseExpr_toExpr_degree_le _ _).trans (hsource source hsourceMem)

/-- The actual compiler preserves the degree of every configured lookup input under selector substitution. -/
theorem topLevel_lookupInput_substitution_degree
    (top : TopLevelCircuit F Config PublicInput)
    (argument : LookupArgument F) (hargument : argument ∈ top.constraintSystem.lookups)
    (expression : Expression F Query) (hexpression : expression ∈ argument.inputs) :
    (substSelectorMap top.selectorMap.lookup expression).degree = expression.degree := by
  apply substSelectorMap_degree_singleton
  intro selector hselector
  obtain ⟨compressed, hlookup, hlength, hroot, _⟩ :=
    top.lookupInputSelectorMap_singleton argument hargument expression hexpression hselector
  exact ⟨compressed, hlookup, hlength, hroot⟩

/-- A source degree bound for lookup inputs survives complete compiler translation. -/
theorem topLevel_lookupInput_degree_le (top : TopLevelCircuit F Config PublicInput) (bound : ℕ)
    (hsource : ∀ argument ∈ top.constraintSystem.lookups,
      ∀ expression ∈ argument.inputs, expression.degree ≤ bound)
    (lookup : Fin top.lookupCount) (expression : Expr F)
    (hexpression : expression ∈ top.verifierCS.lookupInputExprs lookup) :
    expression.degreeBound ≤ bound := by
  rw [TopLevelCircuit.verifierCS_lookupInputExprs, TopLevelCircuit.pinnedCS,
    PinnedConstraintSystem.derive_lookupInputExprs_getD _ _ lookup.val lookup.isLt] at hexpression
  simp only [eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsourceMem, rfl⟩ := List.mem_map.mp hexpression
  have hargument := List.getElem_mem lookup.isLt
  refine (eraseExpr_toExpr_degree_le _ _).trans ?_
  rw [topLevel_lookupInput_substitution_degree top _ hargument source hsourceMem]
  exact hsource _ hargument source hsourceMem

/-- A source degree bound for selector-free lookup tables survives complete compiler translation. -/
theorem topLevel_lookupTable_degree_le (top : TopLevelCircuit F Config PublicInput) (bound : ℕ)
    (hsource : ∀ argument ∈ top.constraintSystem.lookups,
      ∀ expression ∈ argument.tables, expression.degree ≤ bound)
    (lookup : Fin top.lookupCount) (expression : Expr F)
    (hexpression : expression ∈ top.verifierCS.lookupTableExprs lookup) :
    expression.degreeBound ≤ bound := by
  rw [TopLevelCircuit.verifierCS_lookupTableExprs, TopLevelCircuit.pinnedCS,
    PinnedConstraintSystem.derive_lookupTableExprs_getD _ _ lookup.val lookup.isLt] at hexpression
  simp only [eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsourceMem, rfl⟩ := List.mem_map.mp hexpression
  rw [substSelectorMap_eq_of_selectorFree _ source
    ((top.constraintSystem.lookups[lookup.val]).tablesFree source hsourceMem)]
  exact (eraseExpr_toExpr_degree_le _ _).trans
    (hsource _ (List.getElem_mem lookup.isLt) source hsourceMem)

end Zcash.Snark.ZeroKnowledge
