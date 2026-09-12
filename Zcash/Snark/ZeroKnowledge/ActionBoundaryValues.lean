import Zcash.Snark.ZeroKnowledge.ActionSelectorReplacement
import Zcash.Snark.ZeroKnowledge.ActionSelectorMasking
import Zcash.Snark.ZeroKnowledge.ActionSourceMasking
import Zcash.Snark.ZeroKnowledge.ActionQueryMasking
import Zcash.Snark.ZeroKnowledge.ActionPublicData
import Zcash.Snark.ZeroKnowledge.KeygenPartialMasking
import Zcash.Snark.ZeroKnowledge.PlonkKeygenSelectors

/-!
# Actual Action boundary values in the source masking certificates

All fixed values at the initial boundary come from the compiler. At later
boundaries the established placement bound makes every packed selector cell zero.
The root-assignment theorem supplies the initial zero replacement values without
requiring particular columns to be zero or prescribing a concrete packing map.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Supply the actual keygen boundary values to the partial verifier checker. -/
def actionBoundaryFixedKnown (boundary : Fin 8) (query : ℕ) : Option Fp :=
  some (plonkKeygenMaskBoundaryFixed actionCircuit boundary query)

/-- Pull the indexed partial valuation back through the actual compiler query resolver. -/
def actionBoundaryQueryKnown (boundary : Fin 8) (query : Query) : Option Fp :=
  exprPartialPublicValue (actionBoundaryFixedKnown boundary)
    (RichExpression.toExpr (eraseExpr (.var query) actionCircuit.gateQueryState))

/-- A surviving source selector atom has the compiler's zero fallback value. -/
theorem actionBoundaryQueryKnown_selector (boundary : Fin 8) (selector : Selector) :
    actionBoundaryQueryKnown boundary (.selector selector) = some 0 := rfl

/-- Packed fixed queries retain their column indices under Action query resolution. -/
theorem actionBoundaryQueryKnown_fixed
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (boundary : Fin 8) (column : ℕ) (hlower : 14 ≤ column) (hupper : column < 29) :
    actionBoundaryQueryKnown boundary (.fixed ⟨column⟩ 0) =
      some (plonkKeygenMaskBoundaryFixed actionCircuit boundary column) := by
  simp only [actionBoundaryQueryKnown, eraseExpr, RichExpression.toExpr, exprPartialPublicValue,
    actionCircuit_fixIdx_packedColumn hpacked column hlower hupper, actionBoundaryFixedKnown]

/-- Initial packed-query values are read directly from the actual compiled fixed columns. -/
theorem actionBoundaryQueryKnown_initial_fixed
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (column : ℕ) (hlower : 14 ≤ column) (hupper : column < 29) :
    actionBoundaryQueryKnown 0 (.fixed ⟨column⟩ 0) =
      some ((actionCircuit.fixedRows.getD column []).getD 0 0) := by
  rw [actionBoundaryQueryKnown_fixed hpacked 0 column hlower hupper]
  simp [plonkKeygenMaskBoundaryFixed, finFn, hupper,
    plonkFixedQueryOrder_selector ⟨column, hupper⟩ hlower, plonkMaskBoundaryRows, plonkKeygenFixedRows]

/-- The proved Action placement endpoint makes every later packed boundary query zero. -/
theorem actionBoundaryQueryKnown_later_fixed
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (boundary : Fin 8) (hinitial : boundary.val ≠ 0)
    (column : ℕ) (hlower : 14 ≤ column) (hupper : column < 29) :
    actionBoundaryQueryKnown boundary (.fixed ⟨column⟩ 0) = some 0 := by
  rw [actionBoundaryQueryKnown_fixed hpacked boundary column hlower hupper]
  congr 1
  unfold plonkKeygenMaskBoundaryFixed
  split
  · simp only [finFn, hupper, ↓reduceDIte, plonkFixedQueryOrder_selector ⟨column, hupper⟩ hlower]
    exact plonkKeygenFixedRows_selector_zero actionCircuit actionCircuit_numFixedColumns_eq.le
      (actionCircuit_placementEnd_eq_1779.le.trans (by decide)) ⟨column, hupper⟩ hlower
      (plonkMaskBoundaryRows boundary) (plonkMaskBoundaryRows_after_zero boundary hinitial)
  · rfl

/-- All source zero and safety certificates survive actual Action substitution
using the compiler's boundary values. Only the compression count is supplied. -/
theorem actionCircuit_substitutedPartialMaskCertificates
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (boundary : Fin 8) (expression : Expression Fp Query) :
    (sourceExpressionZero (actionSourceMaskZero (decide (boundary.val = 0))) expression = true →
      sourcePartialValue (actionBoundaryQueryKnown boundary)
        (substSelectorMap actionCircuit.selectorMap.lookup expression) = some 0) ∧
    (sourceExpressionMaskSafe (actionSourceMaskZero (decide (boundary.val = 0)))
        (actionSourceMaskSafe (decide (boundary.val = 0))) expression = true →
      sourcePartialMaskSafe (actionBoundaryQueryKnown boundary)
        (actionSourceMaskSafe (decide (boundary.val = 0)))
        (substSelectorMap actionCircuit.selectorMap.lookup expression) = true) := by
  apply substSelectorMap_partialMaskCertificates
  · intro query hquery
    cases query with
    | fixed | advice | «instance» => simp [actionSourceMaskZero] at hquery
    | selector selector =>
        cases hlookup : actionCircuit.selectorMap.lookup selector.index with
        | none =>
            simp only [substSelectorMap, hlookup, sourcePartialValue, actionBoundaryQueryKnown_selector]
        | some compressed =>
            simp only [substSelectorMap, hlookup]
            have hcolumn := actionCircuit_packedSelectorBounds hpacked selector.index compressed hlookup
            by_cases hinitial : boundary.val = 0
            · have hboundary : boundary = 0 := Fin.ext hinitial
              subst boundary
              have hmember : selector.index ∈ actionPreviousRowSelectors := by
                simp only [actionSourceMaskZero, Bool.and_eq_true] at hquery
                simpa using hquery.2
              let valuation : Query → Fp := fun query => (actionBoundaryQueryKnown 0 query).getD 0
              have hknown := actionBoundaryQueryKnown_initial_fixed hpacked
                compressed.packedCol hcolumn.1 hcolumn.2
              have hvalue : valuation (.fixed ⟨compressed.packedCol⟩ 0) =
                  (actionCircuit.fixedRows.getD compressed.packedCol []).getD 0 0 := by
                simp only [valuation, hknown, Option.getD_some]
              rw [selReplacement_sourcePartialValue (actionBoundaryQueryKnown 0) valuation compressed
                (by simp only [valuation, hknown, Option.getD_some])]
              exact congrArg some (actionCircuit_previousSelector_replacement_zero selector.index
                hmember hlookup valuation hvalue)
            · have hknown := actionBoundaryQueryKnown_later_fixed hpacked boundary hinitial
                compressed.packedCol hcolumn.1 hcolumn.2
              rw [selReplacement_sourcePartialValue (actionBoundaryQueryKnown boundary)
                (fun _ => 0) compressed hknown]
              exact congrArg some (selReplacement_eval_of_zero compressed (fun _ => 0) rfl)
  · intro query hquery
    cases query with
    | fixed | advice | «instance» => exact hquery
    | selector selector =>
        simp only [substSelectorMap]
        cases hlookup : actionCircuit.selectorMap.lookup selector.index with
        | none => rfl
        | some compressed => exact selReplacement_sourcePartialMaskSafe _ _ compressed rfl

/-- The actual compiler's boundary values make every certified source expression
pass the verifier's partial masking check. -/
theorem actionCircuit_compiledExpressionMaskSafe_values
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (boundary : Fin 8) (expression : Expression Fp Query)
    (hsource : sourceExpressionMaskSafe (actionSourceMaskZero (decide (boundary.val = 0)))
      (actionSourceMaskSafe (decide (boundary.val = 0))) expression = true) :
    exprPartialMaskInvariant (actionBoundaryFixedKnown boundary)
      (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary))
      (RichExpression.toExpr (eraseExpr (substSelectorMap actionCircuit.selectorMap.lookup expression)
        actionCircuit.gateQueryState)) = true := by
  have hsubstituted := (actionCircuit_substitutedPartialMaskCertificates hpacked boundary expression).2 hsource
  apply (eraseExpr_partialMaskCertificates (actionBoundaryQueryKnown boundary)
    (actionSourceMaskSafe (decide (boundary.val = 0))) actionCircuit.gateQueryState
    (actionBoundaryFixedKnown boundary) (plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary))
    (fun _ => rfl) ?_ _).2 hsubstituted
  intro query hquery
  cases query with
  | fixed | «instance» | selector => rfl
  | advice column rotation =>
      simp only [actionSourceMaskSafe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hquery
      have hboundary : boundary = 0 := Fin.ext hquery.1
      change plonkAdviceQueryRetained (plonkMaskBoundaryRows boundary)
        (actionCircuit.gateQueryState.advIdx column.index rotation) = true
      rw [hboundary]
      exact actionCircuit_advIdx_initial_retained column.index rotation hquery.2

end Zcash.Snark.ZeroKnowledge
