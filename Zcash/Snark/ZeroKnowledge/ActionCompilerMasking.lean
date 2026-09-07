import Zcash.Snark.ZeroKnowledge.ActionDerivedKey
import Zcash.Snark.ZeroKnowledge.ActionExpressionMasking

/-!
# The complete masking check for the compiler-derived Action key

The source certificates and compiler preservation theorems discharge every gate
and lookup expression check. The explicit remaining selector conditions are the
compression count and the placement of the previous-row selectors into the four
columns whose initial values the public-data theorem requires to be zero.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

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

/-- Actual Action key generation supplies the entire expression-side masking check from the two packing conditions. -/
theorem actionReferenceKey_maskBoundaryCheck {G : Type} [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (hprevious : ActionPreviousSelectorPacking) :
    plonkPartialMaskBoundaryCheck (actionReferenceKey (actions := actions) urs hk hpacked)
      plonkSelectorBoundaryKnown = true := by
  have hcertificate (boundary : Fin 8) :=
    castKey_expressionChecks (fun expression => exprPartialMaskInvariant (plonkSelectorBoundaryKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)) expression = true)
      (actionCircuit_referenceShape actions urs.k hk hpacked) (actionCircuit.toVerifierKey urs)
      (actionCircuit_verifierGate_maskBoundaryCheck hpacked hprevious boundary)
      (actionCircuit_verifierLookupInput_maskBoundaryCheck hpacked hprevious boundary)
      (actionCircuit_verifierLookupTable_maskBoundaryCheck hpacked hprevious boundary)
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

end Zcash.Snark.ZeroKnowledge
