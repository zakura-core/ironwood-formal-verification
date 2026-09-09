import Zcash.Snark.ZeroKnowledge.ActionQueryRows
import Zcash.Snark.ZeroKnowledge.ActionQueryMasking

/-!# Exact source valuations for all Action verifier rows
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Resolving a registered fixed query recovers its actual query slot. -/
theorem actionGateQuery_fixed_resolves (index column : ℕ) (rotation : ℤ)
    (hquery : actionCircuit.gateQueryState.fixed[index]? = some (column, rotation)) :
    actionCircuit.gateQueryState.fixIdx column rotation = index := by
  obtain ⟨hindex, rfl, rfl⟩ := actionGateQuery_fixed index column rotation hquery
  have hfind : ∀ query : Fin 29,
      findQuery (List.ofFn (fun j : Fin 29 => ((plonkFixedQueryOrder j).val, (0 : ℤ)))).toArray
        (plonkFixedQueryOrder query).val 0 = some query.val := by decide +kernel
  unfold QueryState.fixIdx
  rw [actionCircuit_gateQueryState_fixed actionCircuit_newFixedCols_eq_fifteen, hfind ⟨index, hindex⟩]
  rfl

/-- Resolving a registered advice query recovers its actual query slot. -/
theorem actionGateQuery_advice_resolves (index column : ℕ) (rotation : ℤ)
    (hquery : actionCircuit.gateQueryState.advice[index]? = some (column, rotation)) :
    actionCircuit.gateQueryState.advIdx column rotation = index := by
  obtain ⟨hindex, rfl, rfl⟩ := actionGateQuery_advice index column rotation hquery
  have hfind : ∀ query : Fin 25,
      findQuery (List.ofFn (fun j : Fin 25 =>
        ((plonkAdviceQueryOrder j).1.val, plonkQueryRotation (plonkAdviceQueryOrder j).2.castSucc))).toArray
        (plonkAdviceQueryOrder query).1.val (plonkQueryRotation (plonkAdviceQueryOrder query).2.castSucc) =
          some query.val := by decide +kernel
  unfold QueryState.advIdx
  rw [actionCircuit_gateQueryState_advice, hfind ⟨index, hindex⟩]
  rfl

/-- Resolving Action's registered instance query recovers its sole query slot. -/
theorem actionGateQuery_instance_resolves (index column : ℕ) (rotation : ℤ)
    (hquery : actionCircuit.gateQueryState.inst[index]? = some (column, rotation)) :
    actionCircuit.gateQueryState.instIdx column rotation = index := by
  obtain ⟨rfl, rfl, rfl⟩ := actionGateQuery_instance index column rotation hquery
  unfold QueryState.instIdx
  rw [← actionCircuit.pinnedQueryState_eq_gateQueryState]
  change (findQuery actionCircuit.instanceQueryLayout.toArray 0 0).getD
    actionCircuit.instanceQueryLayout.toArray.size = 0
  rw [actionCircuit_instanceQueryLayout_eq]
  decide +kernel

/-- Pull arbitrary verifier feeds back through Action's exact query resolver. -/
def actionResolvedQueryValuation (fixed advice instanceFeed : ℕ → Fp) : Query → Fp
  | .fixed column rotation => fixed (actionCircuit.gateQueryState.fixIdx column.index rotation)
  | .advice column rotation => advice (actionCircuit.gateQueryState.advIdx column.index rotation)
  | .instance column rotation => instanceFeed (actionCircuit.gateQueryState.instIdx column.index rotation)
  | .selector _ => 0

/-- The source valuation interprets every registered query, independently of the supplied row values. -/
theorem actionResolvedQueryValuation_interprets (fixed advice instanceFeed : ℕ → Fp) :
    Interprets actionCircuit.gateQueryState fixed advice instanceFeed
      (actionResolvedQueryValuation fixed advice instanceFeed) := by
  constructor
  · intro index column rotation hquery
    simp only [actionResolvedQueryValuation, actionGateQuery_advice_resolves index column rotation hquery]
  · intro index column rotation hquery
    simp only [actionResolvedQueryValuation, actionGateQuery_fixed_resolves index column rotation hquery]
  · intro index column rotation hquery
    simp only [actionResolvedQueryValuation, actionGateQuery_instance_resolves index column rotation hquery]

/-- Packed selectors retain the exact actual fixed-column value on every domain row. -/
theorem actionResolvedQueryValuation_packed {actions : ℕ}
    (inputs : Fin actions → PublicInputs Fp) (row : Fin 2048) (advice instanceFeed : ℕ → Fp)
    (column : ℕ) (hlower : 14 ≤ column) (hupper : column < 29) :
    actionResolvedQueryValuation (plonkFixedRowValues (actionPublicPolynomials inputs) row)
      advice instanceFeed (.fixed ⟨column⟩ 0) =
        (actionCircuit.fixedRows.getD column []).getD row.val 0 := by
  simp only [actionResolvedQueryValuation,
    actionCircuit_fixIdx_packedColumn actionCircuit_newFixedCols_eq_fifteen column hlower hupper,
    actionPublicPolynomials, plonkKeygenPublicPolynomials,
    plonkPublicPolynomialsFromRows_fixedRowValues, finFn, dif_pos hupper,
    plonkFixedQueryOrder_selector ⟨column, hupper⟩ hlower, plonkKeygenFixedRows]

/-- The source placement excludes every selector activation from Action's unused suffix. -/
theorem actionCircuit_selector_inactive_after_placement (selector row : ℕ) (hrow : 1779 ≤ row) :
    (selector, row) ∉ actionCircuit.selectorActivations := by
  intro hactive
  have hbound := FloorPlanner.V1.activation_row_lt_placementEnd actionCircuit.operations hactive
  rw [actionCircuit_placementEnd_eq_1779] at hbound
  omega

end Zcash.Snark.ZeroKnowledge
