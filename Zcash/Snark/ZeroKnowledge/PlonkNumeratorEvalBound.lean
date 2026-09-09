import Zcash.Snark.ZeroKnowledge.PlonkNumeratorEvalCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark

/-- Common access bound includes full private-row interpolation and actual stored lookup-family reads. -/
def plonkNumeratorEvalAccessBudget (costs : FieldOperationCosts)
    (read omegaAccess baseRead pointRead : ℕ) (key : StoredPlonkKey) : ℕ :=
  baseRead + pointRead +
    publicRowEvaluationCostBudget costs baseRead omegaAccess
      (pointRead + omegaAccess + 7 * (costs.multiply + 1) + costs.inverse + 13) +
    2 * key.lookupInputs.length + 2 * key.lookupTables.length + read + 1

/-- Complete numerator evaluation budget, with every observation and constraint calculation included. -/
def plonkNumeratorEvalCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess actions columns baseRead pointRead yRead : ℕ) (key : StoredPlonkKey) : ℕ :=
  let access := plonkNumeratorEvalAccessBudget costs read omegaAccess baseRead pointRead key
  (columns * 3 + 1) +
    storedPlonkHxCostBudget costs node equal read omegaAccess actions columns access pointRead yRead key +
    pointRead + (2048 * (costs.multiply + 1) + 1) + costs.add + costs.negate + costs.multiply + 6

/-- Actual priced row providers discharge all callback costs in the numerator evaluation. -/
theorem plonkNumeratorEvalCosted_cost_le (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (point : Fp × ℕ) (baseRead : ℕ)
    (hinstances : ∀ action row, (instances action row).2 ≤ baseRead)
    (hfixed : ∀ column row, (fixed column row).2 ≤ baseRead)
    (hsigma : ∀ column row, (sigma column row).2 ≤ baseRead)
    (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ baseRead)
    (hch : Challenges.ReadBound ch baseRead) :
    (plonkNumeratorEvalCosted costs node equal read omegaAccess key ch instances fixed sigma rows point).2 ≤
      plonkNumeratorEvalCostBudget costs node equal read omegaAccess actions rows.length baseRead point.2 ch.y.2 key := by
  let points := observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)
  let views := observeColumnRowsCosted costs omegaAccess points rows
  let pointRead := point.2 + omegaAccess + 7 * (costs.multiply + 1) + costs.inverse + 13
  let access := plonkNumeratorEvalAccessBudget costs read omegaAccess baseRead point.2 key
  have hbase : baseRead ≤ access := by dsimp only [access, plonkNumeratorEvalAccessBudget]; omega
  have hpoint : point.2 ≤ access := by dsimp only [access, plonkNumeratorEvalAccessBudget]; omega
  have hkey : read + 2 * key.lookupInputs.length + 2 * key.lookupTables.length + 1 ≤ access := by
    dsimp only [access, plonkNumeratorEvalAccessBudget]
    omega
  have hp (index : Fin 5) : (points index).2 ≤ pointRead := by
    have h := observationPointCosted_cost_le costs (omegaOf 11, omegaAccess) point (0, 1) index
    dsimp only [points, pointRead]
    omega
  have hviews : ∀ column ∈ views.1, ∀ index, (column index).2 ≤ access := by
    intro column hcolumn index
    have h := observeColumnRowsCosted_readBound costs omegaAccess points rows baseRead pointRead
      hrows hp column hcolumn index
    dsimp only [access, plonkNumeratorEvalAccessBudget]
    change (column index).2 ≤ publicRowEvaluationCostBudget costs baseRead omegaAccess
      (point.2 + omegaAccess + 7 * (costs.multiply + 1) + costs.inverse + 13) at h
    omega
  rcases hch with ⟨htheta, hbeta, hgamma, _, _, _, _, _, _, _, _, _⟩
  have hquotient := storedPlonkHxCosted_cost_le costs node equal read omegaAccess key { ch with x := point }
    instances fixed sigma views.1 access hkey
    (fun a r => (hinstances a r).trans hbase) (fun c r => (hfixed c r).trans hbase)
    (fun c r => (hsigma c r).trans hbase) hviews (hbeta.trans hbase) (hgamma.trans hbase)
    hpoint (htheta.trans hbase)
  have hlength : views.1.length = rows.length := observeColumnRowsCosted_length _ _ _ _
  rw [hlength] at hquotient
  have hv := observeColumnRowsCosted_cost_le costs omegaAccess points rows
  have hpower := fieldPowerCosted_cost costs.multiply point.1 2048
  change views.2 ≤ _ at hv
  dsimp only [plonkNumeratorEvalCosted]
  rw [hpower]
  dsimp only [plonkNumeratorEvalCostBudget]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add hv hquotient) _) _) _) _) _) _

end Zcash.Snark.ZeroKnowledge
