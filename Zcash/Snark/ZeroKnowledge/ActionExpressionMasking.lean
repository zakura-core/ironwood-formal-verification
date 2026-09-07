import Zcash.Snark.ZeroKnowledge.ActionSelectorMasking
import Zcash.Snark.ZeroKnowledge.KeygenExpressionMasking
import Zcash.Circuits.Integration.VerifierCS

/-!
# Action masking certificates through the complete expression compiler

Selector substitution, query resolution, and verifier-expression translation
preserve the source certificates. The remaining packing premise concerns only
the nine selectors guarding previous-row reads; the full expression check is
derived from the actual Action source and compiler.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- A source certificate becomes the actual compiled expression's public boundary check. -/
theorem actionCircuit_compiledExpressionMaskSafe
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (hprevious : ActionPreviousSelectorPacking) (boundary : Fin 8) (expression : Expression Fp Query)
    (hsource : sourceExpressionMaskSafe (actionSourceMaskZero (decide (boundary.val = 0)))
      (actionSourceMaskSafe (decide (boundary.val = 0))) expression = true) :
    exprPartialMaskInvariant (plonkSelectorBoundaryKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary))
      (RichExpression.toExpr (eraseExpr (substSelectorMap actionCircuit.selectorMap.lookup expression)
        actionCircuit.gateQueryState)) = true := by
  have hsubstituted :=
    (actionCircuit_substitutedSourceMaskCertificates hpacked hprevious _ expression).2 hsource
  apply (eraseExpr_sourceMaskCertificates (actionPackedMaskZero (decide (boundary.val = 0)))
    (actionSourceMaskSafe (decide (boundary.val = 0))) actionCircuit.gateQueryState
    (plonkSelectorBoundaryKnown boundary) (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary))
    ?_ ?_ _).2 hsubstituted
  · intro query hquery
    cases query with
    | advice | «instance» | selector => simp [actionPackedMaskZero] at hquery
    | fixed column rotation =>
        simp only [actionPackedMaskZero, Bool.and_eq_true, decide_eq_true_eq] at hquery
        obtain ⟨⟨⟨hrotation, hlower⟩, hupper⟩, hzero⟩ := hquery
        subst rotation
        simp only [eraseExpr, RichExpression.toExpr, exprPartialPublicValue,
          actionCircuit_fixIdx_packedColumn hpacked column.index hlower hupper]
        by_cases hinitial : boundary.val = 0
        · have hmember : column.index ∈ plonkInitialMaskColumns := by simpa [hinitial] using hzero
          simp [plonkSelectorBoundaryKnown, hinitial, hmember]
        · simp [plonkSelectorBoundaryKnown, hinitial, Nat.not_lt_of_ge hlower]
  · intro query hquery
    cases query with
    | fixed | «instance» | selector => rfl
    | advice column rotation =>
        simp only [actionSourceMaskSafe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hquery
        have hboundary : boundary = 0 := Fin.ext hquery.1
        change plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)
          (actionCircuit.gateQueryState.advIdx column.index rotation) = true
        rw [hboundary]
        exact actionCircuit_advIdx_initial_retained column.index rotation hquery.2

/-- Every actual compiled Action gate passes the public boundary check under the packing conditions. -/
theorem actionCircuit_verifierGate_maskBoundaryCheck
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (hprevious : ActionPreviousSelectorPacking) (boundary : Fin 8) (expression : Expr Fp)
    (hexpression : expression ∈ actionCircuit.verifierCS.gates) :
    exprPartialMaskInvariant (plonkSelectorBoundaryKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)) expression = true := by
  rw [TopLevelCircuit.verifierCS_gates, TopLevelCircuit.pinnedCS,
    derivePinnedCS_decidableEq_irrel (F := Fp) _ (inferInstance : DecidableEq Fp)] at hexpression
  simp only [PinnedConstraintSystem.derive, projectCS, eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
  exact actionCircuit_compiledExpressionMaskSafe hpacked hprevious boundary source
    (actionCircuit_sourceGateMaskSafe _ source hsource)

/-- Every compiled Action lookup input passes the same public boundary check. -/
theorem actionCircuit_verifierLookupInput_maskBoundaryCheck
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (hprevious : ActionPreviousSelectorPacking) (boundary : Fin 8)
    (lookup : Fin actionCircuit.lookupCount) (expression : Expr Fp)
    (hexpression : expression ∈ actionCircuit.verifierCS.lookupInputExprs lookup) :
    exprPartialMaskInvariant (plonkSelectorBoundaryKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)) expression = true := by
  rw [TopLevelCircuit.verifierCS_lookupInputExprs, TopLevelCircuit.pinnedCS,
    derivePinnedCS_decidableEq_irrel (F := Fp) _ (inferInstance : DecidableEq Fp),
    PinnedConstraintSystem.derive_lookupInputExprs_getD (F := Fp) _ _ lookup.val lookup.isLt] at hexpression
  simp only [eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
  exact actionCircuit_compiledExpressionMaskSafe hpacked hprevious boundary source
    (actionCircuit_sourceLookupInputMaskSafe _ _ (List.getElem_mem lookup.isLt) source hsource)

/-- Every compiled Action lookup table passes the same public boundary check. -/
theorem actionCircuit_verifierLookupTable_maskBoundaryCheck
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (hprevious : ActionPreviousSelectorPacking) (boundary : Fin 8)
    (lookup : Fin actionCircuit.lookupCount) (expression : Expr Fp)
    (hexpression : expression ∈ actionCircuit.verifierCS.lookupTableExprs lookup) :
    exprPartialMaskInvariant (plonkSelectorBoundaryKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)) expression = true := by
  rw [TopLevelCircuit.verifierCS_lookupTableExprs, TopLevelCircuit.pinnedCS,
    derivePinnedCS_decidableEq_irrel (F := Fp) _ (inferInstance : DecidableEq Fp),
    PinnedConstraintSystem.derive_lookupTableExprs_getD (F := Fp) _ _ lookup.val lookup.isLt] at hexpression
  simp only [eraseGates, List.map_map, Function.comp_def] at hexpression
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
  exact actionCircuit_compiledExpressionMaskSafe hpacked hprevious boundary source
    (actionCircuit_sourceLookupTableMaskSafe _ _ (List.getElem_mem lookup.isLt) source hsource)

end Zcash.Snark.ZeroKnowledge
