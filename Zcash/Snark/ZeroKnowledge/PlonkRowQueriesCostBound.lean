import Zcash.Snark.ZeroKnowledge.PlonkRowQueriesCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- One bound covers public queries and complete private-column routing and observation. -/
def plonkRowQueryCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns rowRead pointRead : ℕ) : ℕ :=
  publicRowEvaluationCostBudget costs rowRead omegaAccess
    (pointRead + omegaAccess + 7 * (costs.multiply + 1) + costs.inverse + 13) +
    4 * actions * actions + 260 * actions + 22 * actions * (equal + 2) +
    2 * columns + read + 170

/-- Increasing the point-reader budget preserves the complete query bound. -/
theorem plonkRowQueryCostBudget_mono_point (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns rowRead : ℕ) {small large : ℕ}
    (h : small ≤ large) :
    plonkRowQueryCostBudget costs equal read omegaAccess actions columns rowRead small ≤
      plonkRowQueryCostBudget costs equal read omegaAccess actions columns rowRead large := by
  dsimp only [plonkRowQueryCostBudget, publicRowEvaluationCostBudget]
  gcongr

/-- The original advice reader's bound includes every selected row-polynomial computation. -/
theorem plonkObservedAdviceQueryCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (rows : List (Fin 2048 → Fp × ℕ)) (point : Fp × ℕ) (action : Fin actions) (index : ℕ)
    (rowRead : ℕ) (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ rowRead) :
    (plonkAdviceQueryCosted equal read
      (observeColumnRowsCosted costs omegaAccess
        (observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)) rows).1 action index).2 ≤
      plonkRowQueryCostBudget costs equal read omegaAccess actions rows.length rowRead point.2 := by
  let points := observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)
  let pointRead := point.2 + omegaAccess + 7 * (costs.multiply + 1) + costs.inverse + 13
  have hp (i : Fin 5) : (points i).2 ≤ pointRead := by
    have h := observationPointCosted_cost_le costs (omegaOf 11, omegaAccess) point (0, 1) i
    dsimp only [points, pointRead]
    omega
  have h := plonkAdviceQueryCosted_cost_le equal read
    (observeColumnRowsCosted costs omegaAccess points rows).1 action index
    (publicRowEvaluationCostBudget costs rowRead omegaAccess pointRead)
    (observeColumnRowsCosted_readBound costs omegaAccess points rows rowRead pointRead hrows hp)
  rw [observeColumnRowsCosted_length] at h
  simpa only [plonkRowQueryCostBudget, points, pointRead,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Fixed queries fit the same complete bound, including their finite lookup table. -/
theorem plonkRowFixedQueryCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (index : ℕ)
    (rowRead : ℕ) (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead) :
    (plonkFixedQueryCosted costs omegaAccess fixed point index).2 ≤
      plonkRowQueryCostBudget costs equal read omegaAccess actions columns rowRead point.2 := by
  refine (plonkFixedQueryCosted_cost_le costs omegaAccess fixed point index rowRead hfixed).trans ?_
  dsimp only [plonkRowQueryCostBudget, publicRowEvaluationCostBudget]
  omega

/-- Public instance or sigma queries fit the same bound, including interpolation and evaluation. -/
theorem plonkRowPublicQueryCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns : ℕ) {count : ℕ}
    (rows : Fin count → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (index : ℕ)
    (rowRead : ℕ) (hrows : ∀ column row, (rows column row).2 ≤ rowRead) :
    (publicRowQueryCosted costs omegaAccess rows point index).2 ≤
      plonkRowQueryCostBudget costs equal read omegaAccess actions columns rowRead point.2 := by
  refine (publicRowQueryCosted_cost_le costs omegaAccess rows point index rowRead hrows).trans ?_
  dsimp only [plonkRowQueryCostBudget, publicRowEvaluationCostBudget]
  omega

end Zcash.Snark.ZeroKnowledge
