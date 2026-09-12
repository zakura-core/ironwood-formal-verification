import Zcash.Snark.ZeroKnowledge.PlonkPermutationFactorsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- A selected materialized chunk has at most the total number of stored layout entries. -/
theorem listGetD_length_le_sum {α : Type*} (layout : List (List α)) (index : ℕ) :
    (layout.getD index []).length ≤ (layout.map List.length).sum := by
  have h := getDListCosted_property 0 [] layout
    (fun chunk => chunk.length ≤ (layout.map List.length).sum) (Nat.zero_le _)
    (fun chunk hchunk => listValue_le_map_sum List.length layout chunk hchunk) index
  simpa only [getDListCosted_result] using h

/-- Complete factor-list preparation budget from stored layout, row, and query sizes. -/
def plonkPermutationFactorCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns rowRead rowLimit layoutRead chunks entries : ℕ) : ℕ :=
  let pointRead := omegaAccess + rowLimit * (costs.multiply + 1) + 2
  let access := plonkRowQueryCostBudget costs equal read omegaAccess actions columns rowRead pointRead
  layoutRead + 2 * chunks + read + pointRead + entries * (2 * access + 3 * columns + 7) + 5

/-- Every original factor pair is constructed with its full query and input preparation budget. -/
theorem plonkPermutationFactorRowsCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (action : Fin actions)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (chunk row rowLimit rowRead : ℕ)
    (hrow : row ≤ rowLimit) (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead) (hsigma : ∀ c r, (sigma c r).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ r, (column r).2 ≤ rowRead) :
    (plonkPermutationFactorRowsCosted costs equal read omegaAccess
      instances fixed sigma rows action layout chunk row).2 ≤
      plonkPermutationFactorCostBudget costs equal read omegaAccess actions rows.length rowRead rowLimit
        layout.2 layout.1.length (layout.1.map List.length).sum := by
  let selected := getDListCosted read [] layout.1 chunk
  let power := fieldPowerCosted costs.multiply (omegaOf 11) row
  let point := (power.1, omegaAccess + power.2 + 1)
  let pointRead := omegaAccess + rowLimit * (costs.multiply + 1) + 2
  let access := plonkRowQueryCostBudget costs equal read omegaAccess actions rows.length rowRead pointRead
  let unit := 2 * access + 3 * rows.length + 6
  have hp : point.2 ≤ pointRead := by
    dsimp only [point, power, pointRead]
    rw [fieldPowerCosted_cost]
    have h := Nat.mul_le_mul_right (costs.multiply + 1) hrow
    omega
  have hb := plonkRowQueryCostBudget_mono_point costs equal read omegaAccess actions rows.length rowRead hp
  have hf (entry : ColumnRef × ℕ) (_ : entry ∈ selected.1) :
      (plonkPermutationPairAtPointCosted costs equal read omegaAccess
        instances fixed sigma rows point action entry).2 ≤ unit := by
    have h := plonkPermutationPairAtPointCosted_cost_le costs equal read omegaAccess
      instances fixed sigma rows point action entry rowRead hinstances hfixed hsigma hrows
    dsimp only [unit, access]
    omega
  have hm := mapListCosted_cost_le
    (plonkPermutationPairAtPointCosted costs equal read omegaAccess instances fixed sigma rows point action)
    selected.1 unit hf
  have hl : selected.1.length ≤ (layout.1.map List.length).sum := by
    simpa only [selected, getDListCosted_result] using listGetD_length_le_sum layout.1 chunk
  have hs : selected.2 ≤ 2 * layout.1.length + read + 1 := getDListCosted_cost_le _ _ _ _
  have ht := Nat.mul_le_mul_right (unit + 1) hl
  change layout.2 + selected.2 + point.2 + (mapListCosted
    (plonkPermutationPairAtPointCosted costs equal read omegaAccess instances fixed sigma rows point action)
    selected.1).2 + 3 ≤ _
  change _ ≤ layout.2 + 2 * layout.1.length + read + pointRead +
    (layout.1.map List.length).sum * (2 * access + 3 * rows.length + 7) + 5
  dsimp only [unit] at hm ht
  rw [show 2 * access + 3 * rows.length + 6 + 1 =
    2 * access + 3 * rows.length + 7 by omega] at hm ht
  omega

end Zcash.Snark.ZeroKnowledge
