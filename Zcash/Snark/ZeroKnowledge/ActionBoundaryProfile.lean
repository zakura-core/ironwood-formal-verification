import Zcash.Snark.ZeroKnowledge.ActionBoundaryValues
import Zcash.Snark.ZeroKnowledge.ActionDerivedKey
import Zcash.Circuits.Integration.VerifierCS

/-!
# The Action masking profile from actual compiler values

Every compiled gate and lookup inherits its source masking certificate. The
boundary valuation reads the compiler's fixed rows, so it also handles an
inactive selector sharing a column with an active selector. The source activation
trace and the compression root assignments discharge the initial boundary.

The only supplied selector condition is the number of compressed columns. No
initial fixed-column zeros or particular selector-to-column routing are assumed.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

/-- Every compiled Action gate passes the mask check with actual boundary values. -/
theorem actionCircuit_verifierGate_maskBoundaryCheck_values
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (boundary : Fin 8) (expression : Expr Fp)
    (hexpression : expression ∈ actionCircuit.verifierCS.gates) :
    exprPartialMaskInvariant (actionBoundaryFixedKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)) expression = true := by
  rw [TopLevelCircuit.verifierCS_gates, TopLevelCircuit.pinnedCS,
    derivePinnedCS_decidableEq_irrel (F := Fp) _ (inferInstance : DecidableEq Fp)] at hexpression
  simp only [PinnedConstraintSystem.derive, projectCS, eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
  exact actionCircuit_compiledExpressionMaskSafe_values hpacked boundary source
    (actionCircuit_sourceGateMaskSafe _ source hsource)

/-- Every compiled Action lookup input passes the check with actual boundary values. -/
theorem actionCircuit_verifierLookupInput_maskBoundaryCheck_values
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (boundary : Fin 8) (lookup : Fin actionCircuit.lookupCount) (expression : Expr Fp)
    (hexpression : expression ∈ actionCircuit.verifierCS.lookupInputExprs lookup) :
    exprPartialMaskInvariant (actionBoundaryFixedKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)) expression = true := by
  rw [TopLevelCircuit.verifierCS_lookupInputExprs, TopLevelCircuit.pinnedCS,
    derivePinnedCS_decidableEq_irrel (F := Fp) _ (inferInstance : DecidableEq Fp),
    PinnedConstraintSystem.derive_lookupInputExprs_getD (F := Fp) _ _ lookup.val lookup.isLt] at hexpression
  simp only [eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
  exact actionCircuit_compiledExpressionMaskSafe_values hpacked boundary source
    (actionCircuit_sourceLookupInputMaskSafe _ _ (List.getElem_mem lookup.isLt) source hsource)

/-- Every compiled Action lookup table passes the check with actual boundary values. -/
theorem actionCircuit_verifierLookupTable_maskBoundaryCheck_values
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (boundary : Fin 8) (lookup : Fin actionCircuit.lookupCount) (expression : Expr Fp)
    (hexpression : expression ∈ actionCircuit.verifierCS.lookupTableExprs lookup) :
    exprPartialMaskInvariant (actionBoundaryFixedKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)) expression = true := by
  rw [TopLevelCircuit.verifierCS_lookupTableExprs, TopLevelCircuit.pinnedCS,
    derivePinnedCS_decidableEq_irrel (F := Fp) _ (inferInstance : DecidableEq Fp),
    PinnedConstraintSystem.derive_lookupTableExprs_getD (F := Fp) _ _ lookup.val lookup.isLt] at hexpression
  simp only [eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
  exact actionCircuit_compiledExpressionMaskSafe_values hpacked boundary source
    (actionCircuit_sourceLookupTableMaskSafe _ _ (List.getElem_mem lookup.isLt) source hsource)

/-- Casting a key along a shape equality preserves its expression predicates, transporting compiler
checks to the protocol key. -/
private theorem castKey_expressionChecks {G : Type} {source target : CircuitShape}
    (predicate : Expr Fp → Prop) (hshape : source = target) (key : VerifyingKey source Fp G)
    (hgates : ∀ expression ∈ key.gates, predicate expression)
    (hinputs : ∀ lookup expression, expression ∈ key.lookupInputExprs lookup → predicate expression)
    (htables : ∀ lookup expression, expression ∈ key.lookupTableExprs lookup → predicate expression) :
    (∀ expression ∈ (hshape ▸ key).gates, predicate expression) ∧
    (∀ lookup expression, expression ∈ (hshape ▸ key).lookupInputExprs lookup → predicate expression) ∧
    (∀ lookup expression, expression ∈ (hshape ▸ key).lookupTableExprs lookup → predicate expression) := by
  cases hshape
  exact ⟨hgates, hinputs, htables⟩

/-- The actual Action key passes the complete check using its compiler boundary values. -/
theorem actionReferenceKey_maskBoundaryCheck_values {G : Type}
    [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    plonkPartialMaskBoundaryCheck (actionReferenceKey (actions := actions) urs hk hpacked)
      actionBoundaryFixedKnown = true := by
  have hcertificate (boundary : Fin 8) :=
    castKey_expressionChecks (fun expression => exprPartialMaskInvariant (actionBoundaryFixedKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)) expression = true)
      (actionCircuit_referenceShape actions urs.k hk hpacked) (actionCircuit.toVerifierKey urs)
      (actionCircuit_verifierGate_maskBoundaryCheck_values hpacked boundary)
      (actionCircuit_verifierLookupInput_maskBoundaryCheck_values hpacked boundary)
      (actionCircuit_verifierLookupTable_maskBoundaryCheck_values hpacked boundary)
  simp only [plonkPartialMaskBoundaryCheck, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro boundary _
    exact List.all_eq_true.mpr (hcertificate boundary).1
  · apply List.all_eq_true.mpr
    intro boundary _
    apply List.all_eq_true.mpr
    intro lookup _
    simp only [Bool.and_eq_true]
    constructor
    · exact List.all_eq_true.mpr ((hcertificate (boundary.castLE (by decide))).2.1 lookup)
    · exact List.all_eq_true.mpr ((hcertificate (boundary.castLE (by decide))).2.2 lookup)

/-- The Action compiler and source traces supply the full masking profile, assuming only the compression count. -/
theorem actionReferenceKey_maskingProfile {G : Type}
    [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (inputs : Fin actions → PublicInputs Fp) :
    PlonkMaskingProfile (actionReferenceKey (actions := actions) urs hk hpacked)
      (actionPublicPolynomials inputs) := by
  apply plonkPartialMaskBoundaryCheck_sound _ _ actionBoundaryFixedKnown ?_
    (actionReferenceKey_maskBoundaryCheck_values urs hk hpacked)
  intro boundary query value hvalue
  have hcolumns : 29 ≤ actionCircuit.fixedColumnCount := by
    rw [actionCircuit.fixedColumnCount_eq, actionCircuit_numFixedColumns_eq, hpacked]
  have hagrees := plonkKeygenPublicPolynomials_maskBoundary actionCircuit
    actionCircuit_domainExponent_eq actionCircuit_blindingFactors_eq hcolumns
    (actionInstanceRows inputs) (plonkKeygenSigmaRows actionCircuit) boundary
  exact (congrFun hagrees query).trans (Option.some.inj hvalue)

end Zcash.Snark.ZeroKnowledge
