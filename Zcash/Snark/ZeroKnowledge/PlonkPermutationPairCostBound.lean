import Zcash.Snark.ZeroKnowledge.PlonkPermutationPairCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Both fields of a real permutation pair retain their complete original query costs. -/
theorem plonkPermutationPairAtPointCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (point : Fp × ℕ) (action : Fin actions)
    (entry : ColumnRef × ℕ) (rowRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead)
    (hsigma : ∀ c r, (sigma c r).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ r, (column r).2 ≤ rowRead) :
    (plonkPermutationPairAtPointCosted costs equal read omegaAccess
      instances fixed sigma rows point action entry).2 ≤
      2 * plonkRowQueryCostBudget costs equal read omegaAccess actions rows.length rowRead point.2 +
        3 * rows.length + 6 := by
  let points := observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)
  let views := observeColumnRowsCosted costs omegaAccess points rows
  let access := plonkRowQueryCostBudget costs equal read omegaAccess actions rows.length rowRead point.2
  have hi (i : ℕ) : (publicRowQueryCosted costs omegaAccess
      (fun _ : Fin 1 => instances action) point i).2 ≤ access :=
    plonkRowPublicQueryCosted_cost_le costs equal read omegaAccess actions rows.length
      (fun _ : Fin 1 => instances action) point i rowRead (fun _ r => hinstances action r)
  have ha (i : ℕ) : (plonkAdviceQueryCosted equal read views.1 action i).2 ≤ access :=
    plonkObservedAdviceQueryCosted_cost_le costs equal read omegaAccess rows point action i rowRead hrows
  have hf (i : ℕ) : (plonkFixedQueryCosted costs omegaAccess fixed point i).2 ≤ access :=
    plonkRowFixedQueryCosted_cost_le costs equal read omegaAccess actions rows.length fixed point i rowRead hfixed
  have hs (i : ℕ) : (publicRowQueryCosted costs omegaAccess sigma point i).2 ≤ access :=
    plonkRowPublicQueryCosted_cost_le costs equal read omegaAccess actions rows.length sigma point i rowRead hsigma
  have hp := permutationColumnPairCosted_cost_le
    (publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) point)
    (plonkAdviceQueryCosted equal read views.1 action)
    (plonkFixedQueryCosted costs omegaAccess fixed point)
    (publicRowQueryCosted costs omegaAccess sigma point) entry access hi ha hf hs
  have hv := observeColumnRowsCosted_cost_le costs omegaAccess points rows
  change views.2 ≤ rows.length * 3 + 1 at hv
  change views.2 + (permutationColumnPairCosted
    (publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) point)
    (plonkAdviceQueryCosted equal read views.1 action)
    (plonkFixedQueryCosted costs omegaAccess fixed point)
    (publicRowQueryCosted costs omegaAccess sigma point) entry).2 + 1 ≤ _
  change _ ≤ 2 * access + 3 * rows.length + 6
  omega

end Zcash.Snark.ZeroKnowledge
