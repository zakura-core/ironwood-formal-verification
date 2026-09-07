import Zcash.Snark.ZeroKnowledge.PlonkKeygenSelectors

/-!
# Advice independence after selector placement

The partial public information is the same as at the noninitial masking boundaries:
all packed selectors are zero, and the fourteen original fixed columns are unknown.
Here every advice query is allowed to change. The compiler supplies this information
at any row after its placement endpoint, including usable rows before suffix masking.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Halo2

/-- Check that gates and both sides of every lookup ignore advice when all packed selectors are zero. -/
def plonkInactiveExpressionsCheck {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) : Bool :=
  let check := exprPartialMaskInvariant (plonkSelectorBoundaryKnown 1) (fun _ => false)
  vk.gates.all check && (List.finRange 3).all fun lookup =>
    (vk.lookupInputExprs lookup).all check && (vk.lookupTableExprs lookup).all check

/-- The finite certificate supplies its individual gate and lookup checks. -/
theorem plonkInactiveExpressionsCheck_sound {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (hcheck : plonkInactiveExpressionsCheck (actions := actions) (k := k) vk = true) :
    (∀ expr ∈ vk.gates, exprPartialMaskInvariant (plonkSelectorBoundaryKnown 1) (fun _ => false) expr = true) ∧
      (∀ lookup : Fin 3, ∀ expr ∈ vk.lookupInputExprs lookup,
        exprPartialMaskInvariant (plonkSelectorBoundaryKnown 1) (fun _ => false) expr = true) ∧
      (∀ lookup : Fin 3, ∀ expr ∈ vk.lookupTableExprs lookup,
        exprPartialMaskInvariant (plonkSelectorBoundaryKnown 1) (fun _ => false) expr = true) := by
  let check := exprPartialMaskInvariant (plonkSelectorBoundaryKnown 1) (fun _ => false)
  have h : vk.gates.all check = true ∧
      (List.finRange 3).all (fun lookup =>
        (vk.lookupInputExprs lookup).all check && (vk.lookupTableExprs lookup).all check) = true := by
    simpa only [plonkInactiveExpressionsCheck, check, Bool.and_eq_true] using hcheck
  have hlookup (lookup : Fin 3) :
      (vk.lookupInputExprs lookup).all check = true ∧ (vk.lookupTableExprs lookup).all check = true := by
    simpa only [Bool.and_eq_true] using List.all_eq_true.mp h.2 lookup (List.mem_finRange lookup)
  exact ⟨List.all_eq_true.mp h.1,
    fun lookup => List.all_eq_true.mp (hlookup lookup).1,
    fun lookup => List.all_eq_true.mp (hlookup lookup).2⟩

/-- Compiler fixed rows agree with the zero-selector information after placement. -/
theorem plonkKeygenPublicPolynomials_inactive_agrees {actions : ℕ}
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (hk : top.domainExponent = 11) (hcolumns : 29 ≤ top.fixedColumnCount)
    (hprefix : top.constraintSystem.numFixedColumns ≤ 14)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (row : Fin 2048) (hplacement : FloorPlanner.V1.placementEnd top.operations ≤ row.val)
    (query : ℕ) (value : Fp) (hknown : plonkSelectorBoundaryKnown 1 query = some value) :
    plonkFixedRowValues (plonkKeygenPublicPolynomials top instances sigma) row query = value := by
  rw [plonkKeygenPublicPolynomials, plonkPublicPolynomialsFromRows_fixedRowValues]
  by_cases hsmall : query < 14
  · simp [plonkSelectorBoundaryKnown, hsmall] at hknown
  have hvalue : (0 : Fp) = value := by
    simpa [plonkSelectorBoundaryKnown, hsmall] using hknown
  by_cases hquery : query < 29
  · have hselector : 14 ≤ query := Nat.le_of_not_gt hsmall
    simp only [finFn, hquery, ↓reduceDIte]
    rw [plonkFixedQueryOrder_selector ⟨query, hquery⟩ hselector]
    exact (topLevelSelectorRows_zero_of_placementEnd_le top query row.val
      (hprefix.trans hselector) (hquery.trans_le hcolumns)
      (by simpa only [TopLevelCircuit.n, hk] using row.isLt) hplacement).trans hvalue
  · simpa [finFn, hquery] using hvalue

/-- An inactive expression has the same value for arbitrary private row states. -/
theorem plonkInactiveExpressionRowValue_eq {actions : ℕ}
    (pub : PlonkPublicPolynomials actions) (left right : ColumnHistory 2048)
    (a : Fin actions) (row : Fin 2048) (expr : Expr Fp)
    (hagrees : ∀ query value, plonkSelectorBoundaryKnown 1 query = some value →
      plonkFixedRowValues pub row query = value)
    (hcheck : exprPartialMaskInvariant (plonkSelectorBoundaryKnown 1) (fun _ => false) expr = true) :
    plonkExpressionRowValue pub left a row expr = plonkExpressionRowValue pub right a row expr :=
  exprMaskInvariant_sound _ _ (fun _ => false) _ _ (by intro query h; cases h) expr
    (exprPartialMaskInvariant_refines _ _ hagrees (fun _ => false) expr hcheck)

end Zcash.Snark.ZeroKnowledge
