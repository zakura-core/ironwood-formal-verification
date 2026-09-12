import Zcash.Snark.ZeroKnowledge.RowObservationCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Evaluate a private polynomial by the original column route and complete row computation. -/
def privateColumnPolynomialEvalCosted (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (rows : List (Fin 2048 → Fp × ℕ)) (id : PrivateColumnId actions) (point : Fp × ℕ) : Fp × ℕ :=
  let views := observeColumnRowsCosted costs omegaAccess (fun _ : Fin 1 => point) rows
  let value := privateColumnViewCosted equal read views.1 id 0
  (value.1, views.2 + value.2 + 1)

/-- Erasure includes the original missing-column zero polynomial. -/
theorem privateColumnPolynomialEvalCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (rows : List (Fin 2048 → Fp × ℕ)) (id : PrivateColumnId actions) (point : Fp × ℕ) :
    (privateColumnPolynomialEvalCosted costs equal read omegaAccess rows id point).1 =
      (privateColumnPolynomial (rows.map (fun column row => (column row).1)) id).eval point.1 := by
  simp only [privateColumnPolynomialEvalCosted, privateColumnViewCosted_result,
    observeColumnRowsCosted_result, privateColumnView_observe]

/-- Complete budget for private routing, closure preparation, interpolation, and evaluation. -/
def privateColumnPolynomialEvalCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns rowRead pointRead : ℕ) : ℕ :=
  publicRowEvaluationCostBudget costs rowRead omegaAccess pointRead +
    4 * actions * actions + 260 * actions + 22 * actions * (equal + 2) +
    5 * columns + read + 17

/-- Every callback retained in the evaluator is discharged by its full row-polynomial bound. -/
theorem privateColumnPolynomialEvalCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (rows : List (Fin 2048 → Fp × ℕ)) (id : PrivateColumnId actions) (point : Fp × ℕ)
    (rowRead : ℕ) (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ rowRead) :
    (privateColumnPolynomialEvalCosted costs equal read omegaAccess rows id point).2 ≤
      privateColumnPolynomialEvalCostBudget costs equal read omegaAccess actions rows.length rowRead point.2 := by
  let views := observeColumnRowsCosted costs omegaAccess (fun _ : Fin 1 => point) rows
  have hv := observeColumnRowsCosted_cost_le costs omegaAccess (fun _ : Fin 1 => point) rows
  have hr := privateColumnViewCosted_cost_le equal read views.1 id 0
    (publicRowEvaluationCostBudget costs rowRead omegaAccess point.2)
    (observeColumnRowsCosted_readBound costs omegaAccess (fun _ : Fin 1 => point)
      rows rowRead point.2 hrows (fun _ => le_rfl))
  have hl : views.1.length = rows.length := observeColumnRowsCosted_length _ _ _ _
  rw [hl] at hr
  change views.2 ≤ rows.length * 3 + 1 at hv
  change views.2 + (privateColumnViewCosted equal read views.1 id 0).2 + 1 ≤ _
  dsimp only [privateColumnPolynomialEvalCostBudget]
  omega

/-- Increasing a supplied point-access budget preserves the complete private-evaluation bound. -/
theorem privateColumnPolynomialEvalCostBudget_mono_point (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns rowRead : ℕ) {small large : ℕ} (h : small ≤ large) :
    privateColumnPolynomialEvalCostBudget costs equal read omegaAccess actions columns rowRead small ≤
      privateColumnPolynomialEvalCostBudget costs equal read omegaAccess actions columns rowRead large := by
  dsimp only [privateColumnPolynomialEvalCostBudget, publicRowEvaluationCostBudget]
  gcongr

end Zcash.Snark.ZeroKnowledge
