import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Complete polynomial budget for all stored private columns and the original selected row-mask tape. -/
def plonkStoredColumnsCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare actions tapeSize publicRowRead witnessRead
      thetaRead betaRead gammaRead : ℕ) (stored : StoredPlonkKey) : ℕ :=
  let columnBound := plonkStoredColumnCostBudget costs node equal read omegaAccess canonicalRead compare
    actions (22 * actions) publicRowRead witnessRead thetaRead betaRead gammaRead stored
  let tapeRead := 2 * tapeSize + read + 1
  (4 * actions * actions + 414 * actions + 12) +
    (22 * actions) * (columnBound + 2048 * (2 * 2048 + read + tapeRead + 6) + 2048 * 2048 + 6) + 2

/-- The complete real private-column runtime uses bounded stored histories and preserves every masking dependency. -/
theorem plonkStoredColumnsFromTapeCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (tape : List Fp) (publicRowRead witnessRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ publicRowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ publicRowRead) (hsigma : ∀ c r, (sigma c r).2 ≤ publicRowRead)
    (hwitness : ∀ a c r, (witness a c r).2 ≤ witnessRead) :
    (plonkStoredColumnsFromTapeCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma tape).2 ≤
      plonkStoredColumnsCostBudget costs node equal read omegaAccess canonicalRead compare actions tape.length
        publicRowRead witnessRead theta.2 beta.2 gamma.2 stored := by
  let construct := plonkStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma
  let columnBound := plonkStoredColumnCostBudget costs node equal read omegaAccess canonicalRead compare
    actions (22 * actions) publicRowRead witnessRead theta.2 beta.2 gamma.2 stored
  let tapeRead := 2 * tape.length + read + 1
  have hc (id : PrivateColumnId actions) (earlier : List (List Fp)) (hl : earlier.length ≤ 22 * actions)
      (hr : ∀ values ∈ earlier, values.length ≤ 2048) : (construct id earlier).2 ≤ columnBound :=
    (plonkStoredColumnCosted_cost_le costs node equal read omegaAccess canonicalRead compare stored
      instances fixed sigma witness theta beta gamma id earlier publicRowRead witnessRead
      hinstances hfixed hsigma hwitness hr).trans
      (plonkStoredColumnCostBudget_mono_columns costs node equal read omegaAccess canonicalRead compare
        actions publicRowRead witnessRead theta.2 beta.2 gamma.2 stored hl)
  have hw (id : PrivateColumnId actions) (earlier : List (List Fp)) : (construct id earlier).1.length = 2048 :=
    plonkStoredColumnCosted_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have ht (index : ℕ) : (getDListCosted read (0 : Fp) tape index).2 ≤ tapeRead :=
    getDListCosted_cost_le _ _ _ _
  have hn : ([] : List (List Fp)).length + (privateColumnRecipesCosted actions).1.length ≤ 22 * actions := by
    rw [privateColumnRecipesCosted_length]
    simp
  have hr := storedColumnRowsFromTapeCosted_cost_le 2048 read construct
    (privateColumnRecipesCosted actions).1 [] (getDListCosted read 0 tape) 0 (22 * actions) columnBound tapeRead
    hw hc ht hn (by simp)
  rw [privateColumnRecipesCosted_length] at hr
  have hp := privateColumnRecipesCosted_cost_le actions
  change (privateColumnRecipesCosted actions).2 + (storedColumnRowsFromTapeCosted 2048 read construct
    (privateColumnRecipesCosted actions).1 [] (getDListCosted read 0 tape) 0).2 + 1 ≤ _
  calc
    _ ≤ (4 * actions * actions + 414 * actions + 12) +
        ((22 * actions) * (columnBound + 2048 * (2 * 2048 + read + tapeRead + 6) + 2048 * 2048 + 6) + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add hp hr) 1
    _ = _ := by dsimp only [plonkStoredColumnsCostBudget, columnBound, tapeRead]; ring

end Zcash.Snark.ZeroKnowledge
