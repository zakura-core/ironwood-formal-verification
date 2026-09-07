import Zcash.Snark.ZeroKnowledge.ActionExpressionDegree
import Zcash.Snark.ZeroKnowledge.SelectorReplacementDegree

/-!
# The actual Action key's complete degree profile

The compressor's proved per-selector budget bounds every packed replacement,
independently of activation conflicts. A kernel reduction of the Action source
expressions at those maximum costs gives degree nine. Query resolution then
transports that bound to the actual verifier gates. Together with the compiled
lookup bounds and permutation widths, this discharges the full degree profile.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

/-- Maximum replacement costs allowed by the proved source degrees and Action's degree-nine budget. -/
def actionSelectorDegreeCost (selector : ℕ) : ℕ :=
  selectorCompressionDegreeBudget 9 actionSelectorDegrees[selector]!

/-- The reduced degree vector is bounded by nine, including zero padding outside allocated selectors. -/
theorem actionSelectorDegrees_le (selector : ℕ) : actionSelectorDegrees[selector]! ≤ 9 := by
  by_cases hselector : selector < 56
  · have h : ∀ selector : Fin 56, actionSelectorDegrees[selector.val]! ≤ 9 := by decide +kernel
    exact h ⟨selector, hselector⟩
  · rw [getElem!_neg actionSelectorDegrees selector (by
      change ¬selector < 56
      exact hselector)]
    decide

/-- Even an unallocated selector's fallback query fits its source cost. -/
theorem actionSelectorDegreeCost_pos (selector : ℕ) : 1 ≤ actionSelectorDegreeCost selector := by
  have hdegree := actionSelectorDegrees_le selector
  unfold actionSelectorDegreeCost selectorCompressionDegreeBudget
  split <;> omega

set_option maxRecDepth 10000 in
/-- All Action source gates fit degree nine even at each selector's largest permitted replacement degree. -/
theorem actionCircuit_weightedGateDegrees :
    (flatGates actionCircuit.constraintSystem).all
      (fun expression => selectorWeightedDegree actionSelectorDegreeCost expression ≤ 9) = true := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- Every actual packed selector replacement respects its cost, without an assumed packing trace. -/
theorem actionCircuit_selectorReplacement_degree_le (selector : ℕ) (compressed : SelCompress)
    (hlookup : actionCircuit.selectorMap.lookup selector = some compressed) :
    (selReplacement (F := Fp) compressed).degree ≤ actionSelectorDegreeCost selector := by
  have hdegree : csDegree actionCircuit.constraintSystem = 9 :=
    actionCircuit.constraintSystem_csDegree.trans actionCircuit_constraintDegree_eq
  have h := deriveSelCompressMap_lookup_degree_budget actionCircuit.constraintSystem
    actionCircuit.n actionCircuit.selectorActivations (by rw [hdegree]; decide)
    (by
      intro selector _
      rw [hdegree, actionCircuit_selectorMaxDegrees]
      exact actionSelectorDegrees_le selector) selector compressed
    (by simpa only [← actionCircuit.selectorMap_eq_derive] using hlookup)
  rw [hdegree, actionCircuit_selectorMaxDegrees] at h
  exact (selReplacement_degree_le compressed h.1 h.2.1).trans h.2.2

/-- Selector substitution keeps every actual Action source gate within degree nine. -/
theorem actionCircuit_substitutedGate_degree_le (expression : Expression Fp Query)
    (hexpression : expression ∈ flatGates actionCircuit.constraintSystem) :
    (substSelectorMap actionCircuit.selectorMap.lookup expression).degree ≤ 9 := by
  have hweighted := List.all_eq_true.mp actionCircuit_weightedGateDegrees expression hexpression
  refine (substSelectorMap_degree_le_weighted actionCircuit.selectorMap.lookup
    actionSelectorDegreeCost expression ?_).trans (of_decide_eq_true hweighted)
  intro selector _
  cases hlookup : actionCircuit.selectorMap.lookup selector with
  | none => exact actionSelectorDegreeCost_pos selector
  | some compressed => exact actionCircuit_selectorReplacement_degree_le selector compressed hlookup

/-- The actual compiler's verifier gates satisfy the reference degree bound. -/
theorem actionCircuit_verifierGate_degree_le (expression : Expr Fp)
    (hexpression : expression ∈ actionCircuit.verifierCS.gates) : expression.degreeBound ≤ 9 :=
  topLevel_gate_degree_le actionCircuit 9 actionCircuit_substitutedGate_degree_le expression hexpression

private theorem castKey_gateDegrees {G : Type} {source target : CircuitShape}
    (hshape : source = target) (key : VerifyingKey source Fp G)
    (hgate : ∀ expression ∈ key.gates, expression.degreeBound ≤ 9) :
    ∀ expression ∈ (hshape ▸ key).gates, expression.degreeBound ≤ 9 := by
  cases hshape
  exact hgate

/-- Transport to the reference shape preserves the actual compiler's custom-gate bound. -/
theorem actionReferenceKey_gateDegrees {G : Type} [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11) (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    ∀ expression ∈ (actionReferenceKey (actions := actions) urs hk hpacked).gates,
      expression.degreeBound ≤ 9 :=
  castKey_gateDegrees _ _ actionCircuit_verifierGate_degree_le

/-- All four degree-profile fields now follow from the actual Action configuration and compiler. -/
theorem actionReferenceKey_degreeProfile {G : Type} [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11) (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    PlonkDegreeProfile (actions := actions) (actionReferenceKey urs hk hpacked) :=
  actionReferenceKey_degreeProfile_of_gates (actions := actions) urs hk hpacked
    (actionReferenceKey_gateDegrees (actions := actions) urs hk hpacked)

end Zcash.Snark.ZeroKnowledge
