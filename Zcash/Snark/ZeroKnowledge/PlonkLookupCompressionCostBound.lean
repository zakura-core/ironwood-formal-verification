import Zcash.Snark.ZeroKnowledge.PlonkLookupCompressionCost
import Zcash.Snark.ZeroKnowledge.PlonkRowQueriesCostBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Complete lookup compression budget, polynomial in row, history, and expression sizes. -/
def plonkLookupCompressionCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess actions columns rowRead thetaRead rowLimit : ℕ)
    (exprs : List (Expr Fp)) : ℕ :=
  let pointRead := omegaAccess + rowLimit * (costs.multiply + 1) + 2
  let access := plonkRowQueryCostBudget costs equal read omegaAccess actions columns rowRead pointRead
  (exprs.map exprNodeCount).sum * (node + 1 + access + costs.add + costs.negate + costs.multiply) +
    exprs.length * (thetaRead + costs.multiply + costs.add + 2) + pointRead + 3 * columns + 5

/-- The bound retains all original query readers and complete AST and Horner work. -/
theorem plonkLookupCompressedRowsCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta : Fp × ℕ)
    (action : Fin actions) (exprs : List (Expr Fp)) (row rowLimit rowRead : ℕ)
    (hrow : row ≤ rowLimit)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ r, (column r).2 ≤ rowRead) :
    (plonkLookupCompressedRowsCosted costs node equal read omegaAccess
      instances fixed rows theta action exprs row).2 ≤
      plonkLookupCompressionCostBudget costs node equal read omegaAccess actions
        rows.length rowRead theta.2 rowLimit exprs := by
  let power := fieldPowerCosted costs.multiply (omegaOf 11) row
  let point := (power.1, omegaAccess + power.2 + 1)
  let points := observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)
  let views := observeColumnRowsCosted costs omegaAccess points rows
  let pointRead := omegaAccess + rowLimit * (costs.multiply + 1) + 2
  let access := plonkRowQueryCostBudget costs equal read omegaAccess actions rows.length rowRead pointRead
  have hp : point.2 ≤ pointRead := by
    dsimp only [point, power, pointRead]
    rw [fieldPowerCosted_cost]
    have h := Nat.mul_le_mul_right (costs.multiply + 1) hrow
    omega
  have hb : plonkRowQueryCostBudget costs equal read omegaAccess actions rows.length rowRead point.2 ≤
      access := plonkRowQueryCostBudget_mono_point costs equal read omegaAccess
        actions rows.length rowRead hp
  have hf (i : ℕ) : (plonkFixedQueryCosted costs omegaAccess fixed point i).2 ≤ access :=
    (plonkRowFixedQueryCosted_cost_le costs equal read omegaAccess actions rows.length
      fixed point i rowRead hfixed).trans hb
  have ha (i : ℕ) : (plonkAdviceQueryCosted equal read views.1 action i).2 ≤ access :=
    (plonkObservedAdviceQueryCosted_cost_le costs equal read omegaAccess
      rows point action i rowRead hrows).trans hb
  have hi (i : ℕ) : (publicRowQueryCosted costs omegaAccess
      (fun _ : Fin 1 => instances action) point i).2 ≤ access :=
    (plonkRowPublicQueryCosted_cost_le costs equal read omegaAccess actions rows.length
      (fun _ : Fin 1 => instances action) point i rowRead (fun _ r => hinstances action r)).trans hb
  have hc := compressExprsCosted_cost_le node costs.add costs.negate costs.multiply
    (plonkFixedQueryCosted costs omegaAccess fixed point)
    (plonkAdviceQueryCosted equal read views.1 action)
    (publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) point)
    theta exprs access hf ha hi
  have hv := observeColumnRowsCosted_cost_le costs omegaAccess points rows
  change point.2 + views.2 + (compressExprsCosted node costs.add costs.negate costs.multiply
    (plonkFixedQueryCosted costs omegaAccess fixed point)
    (plonkAdviceQueryCosted equal read views.1 action)
    (publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) point) theta exprs).2 + 2 ≤ _
  change _ ≤ (exprs.map exprNodeCount).sum *
      (node + 1 + access + costs.add + costs.negate + costs.multiply) +
    exprs.length * (theta.2 + costs.multiply + costs.add + 2) + pointRead + 3 * rows.length + 5
  change views.2 ≤ rows.length * 3 + 1 at hv
  omega

end Zcash.Snark.ZeroKnowledge
