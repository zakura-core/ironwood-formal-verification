import Zcash.Snark.ZeroKnowledge.ActionConfiguration
import Zcash.Snark.ZeroKnowledge.PlonkPartialMaskBoundary

/-!
# Action query resolution at mask boundaries

The compiler's query arrays come from the proved Action configure order. Packed
selector columns resolve to the identically numbered fixed-query slots. Current
and next advice queries are retained at row zero, including the compiler's
out-of-range fallback for an unregistered query.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action

/-- The expression compiler's advice array has the proved Action query order. -/
theorem actionCircuit_gateQueryState_advice :
    actionCircuit.gateQueryState.advice =
      (List.ofFn (fun j : Fin 25 =>
        ((plonkAdviceQueryOrder j).1.val, plonkQueryRotation (plonkAdviceQueryOrder j).2.castSucc))).toArray := by
  have hlist := (queryWalkInit_advice actionCircuit.constraintSystem actionCircuit.selectorMap).trans
    (actionCircuit.adviceQueryLayout_eq_constraintSystem.symm.trans actionCircuit_adviceQueryLayout_eq)
  simpa only [Array.toArray_toList] using congrArg List.toArray hlist

/-- The expression compiler's fixed array has the reference order once the compression count is supplied. -/
theorem actionCircuit_gateQueryState_fixed
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    actionCircuit.gateQueryState.fixed =
      (List.ofFn (fun j : Fin 29 => ((plonkFixedQueryOrder j).val, (0 : ℤ)))).toArray := by
  have hlist := actionCircuit.fixedQueryLayout_eq_gateQueryState.symm.trans
    (actionCircuit_fixedQueryLayout_of_selectorCount hpacked)
  simpa only [Array.toArray_toList] using congrArg List.toArray hlist

/-- Each packed Action selector column resolves to the fixed-query slot with the same number. -/
theorem actionCircuit_fixIdx_packedColumn
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) (column : ℕ)
    (hlower : 14 ≤ column) (hupper : column < 29) :
    actionCircuit.gateQueryState.fixIdx column 0 = column := by
  have hfind : ∀ column : Fin 29, 14 ≤ column.val →
      findQuery (List.ofFn (fun j : Fin 29 => ((plonkFixedQueryOrder j).val, (0 : ℤ)))).toArray
        column.val 0 = some column.val := by decide +kernel
  unfold QueryState.fixIdx
  rw [actionCircuit_gateQueryState_fixed hpacked, hfind ⟨column, hupper⟩ hlower]
  rfl

/-- Resolving a current or next advice query never reads a masked cell at row zero. -/
theorem actionCircuit_advIdx_initial_retained (column : ℕ) (rotation : ℤ)
    (hrotation : rotation = 0 ∨ rotation = 1) :
    plonkAdviceQueryRetained 0 (actionCircuit.gateQueryState.advIdx column rotation) = true := by
  have hretained : ∀ query : Fin 25,
      (plonkQueryRotation (plonkAdviceQueryOrder query).2.castSucc = 0 ∨
        plonkQueryRotation (plonkAdviceQueryOrder query).2.castSucc = 1) →
      plonkAdviceQueryRetained 0 query.val = true := by decide +kernel
  unfold QueryState.advIdx
  rw [actionCircuit_gateQueryState_advice]
  cases hfind : findQuery
      (List.ofFn (fun j : Fin 25 =>
        ((plonkAdviceQueryOrder j).1.val, plonkQueryRotation (plonkAdviceQueryOrder j).2.castSucc))).toArray
      column rotation with
  | none => rfl
  | some index =>
      unfold findQuery at hfind
      obtain ⟨hindex, hentry, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfind
      have hbound : index < 25 := by simpa using hindex
      have hqueryRotation : plonkQueryRotation (plonkAdviceQueryOrder ⟨index, hbound⟩).2.castSucc = rotation := by
        simpa only [List.getElem_toArray, List.getElem_ofFn] using (of_decide_eq_true hentry).2
      exact hretained ⟨index, hbound⟩ (hqueryRotation ▸ hrotation)

end Zcash.Snark.ZeroKnowledge
