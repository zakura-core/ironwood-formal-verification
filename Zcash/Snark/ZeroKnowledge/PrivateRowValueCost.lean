import Zcash.Snark.ZeroKnowledge.PrivatePolynomialEvalCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Evaluate an actual private column at a row point, including construction of that point. -/
def privateColumnRowValueCosted (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (rows : List (Fin 2048 → Fp × ℕ)) (id : PrivateColumnId actions) (row : ℕ) : Fp × ℕ :=
  let power := fieldPowerCosted costs.multiply (omegaOf 11) row
  let point := (power.1, omegaAccess + power.2 + 1)
  let value := privateColumnPolynomialEvalCosted costs equal read omegaAccess rows id point
  (value.1, point.2 + value.2 + 1)

/-- The complete reader gives precisely the reference column polynomial at the row point. -/
theorem privateColumnRowValueCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (rows : List (Fin 2048 → Fp × ℕ)) (id : PrivateColumnId actions) (row : ℕ) :
    (privateColumnRowValueCosted costs equal read omegaAccess rows id row).1 =
      (privateColumnPolynomial (rows.map (fun column r => (column r).1)) id).eval (omegaOf 11 ^ row) := by
  simp only [privateColumnRowValueCosted, privateColumnPolynomialEvalCosted_result, fieldPowerCosted_result]

/-- Uniform private-row read budget through the supplied row limit. -/
def privateColumnRowValueCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns rowRead rowLimit : ℕ) : ℕ :=
  let pointRead := omegaAccess + rowLimit * (costs.multiply + 1) + 2
  privateColumnPolynomialEvalCostBudget costs equal read omegaAccess actions columns rowRead pointRead +
    pointRead + 1

/-- Complete field, routing, and row-polynomial work is polynomial in the supplied sizes. -/
theorem privateColumnRowValueCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (rows : List (Fin 2048 → Fp × ℕ)) (id : PrivateColumnId actions) (row rowLimit rowRead : ℕ)
    (hrow : row ≤ rowLimit) (hrows : ∀ column ∈ rows, ∀ r, (column r).2 ≤ rowRead) :
    (privateColumnRowValueCosted costs equal read omegaAccess rows id row).2 ≤
      privateColumnRowValueCostBudget costs equal read omegaAccess actions rows.length rowRead rowLimit := by
  let power := fieldPowerCosted costs.multiply (omegaOf 11) row
  let point := (power.1, omegaAccess + power.2 + 1)
  let pointRead := omegaAccess + rowLimit * (costs.multiply + 1) + 2
  have hp : point.2 ≤ pointRead := by
    dsimp only [point, power, pointRead]
    rw [fieldPowerCosted_cost]
    have h := Nat.mul_le_mul_right (costs.multiply + 1) hrow
    omega
  have hv := privateColumnPolynomialEvalCosted_cost_le costs equal read omegaAccess rows id point rowRead hrows
  have hb := privateColumnPolynomialEvalCostBudget_mono_point costs equal read omegaAccess
    actions rows.length rowRead hp
  change point.2 + (privateColumnPolynomialEvalCosted costs equal read omegaAccess rows id point).2 + 1 ≤ _
  change _ ≤ privateColumnPolynomialEvalCostBudget costs equal read omegaAccess actions rows.length rowRead pointRead +
    pointRead + 1
  omega

end Zcash.Snark.ZeroKnowledge
