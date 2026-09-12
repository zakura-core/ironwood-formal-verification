import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Every stored-column read is bounded by its actual stored width, without recursive reconstruction. -/
theorem plonkStoredColumnCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (List Fp)) (publicRowRead witnessRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ publicRowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ publicRowRead) (hsigma : ∀ c r, (sigma c r).2 ≤ publicRowRead)
    (hwitness : ∀ a c r, (witness a c r).2 ≤ witnessRead)
    (hrows : ∀ values ∈ history, values.length ≤ 2048) :
    (plonkStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma id history).2 ≤
      plonkStoredColumnCostBudget costs node equal read omegaAccess canonicalRead compare actions history.length
        publicRowRead witnessRead theta.2 beta.2 gamma.2 stored := by
  let readers := storedRowReadersCosted read (0 : Fp) 2048 history
  let rowRead := publicRowRead + 4097 + read
  have hi (a : Fin actions) (r : Fin 2048) : (instances a r).2 ≤ rowRead :=
    (hinstances a r).trans (by dsimp only [rowRead]; omega)
  have hf (c : Fin 29) (r : Fin 2048) : (fixed c r).2 ≤ rowRead :=
    (hfixed c r).trans (by dsimp only [rowRead]; omega)
  have hs (c : Fin 15) (r : Fin 2048) : (sigma c r).2 ≤ rowRead :=
    (hsigma c r).trans (by dsimp only [rowRead]; omega)
  have hr (column : Fin 2048 → Fp × ℕ) (hc : column ∈ readers.1) (r : Fin 2048) :
      (column r).2 ≤ rowRead := by
    have h := storedRowReadersCosted_readBound read (0 : Fp) 2048 history 2048 hrows column hc r
    dsimp only [rowRead]
    omega
  have hp := storedRowReadersCosted_cost_le read (0 : Fp) 2048 history
  have hc := plonkConstructStoredColumnCosted_cost_le costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma id readers.1 rowRead witnessRead hi hf hs hwitness hr
  have hl : readers.1.length = history.length := storedRowReadersCosted_length _ _ _ _
  rw [hl] at hc
  change readers.2 ≤ history.length * 3 + 1 at hp
  change readers.2 + (plonkConstructStoredColumnCosted costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma id readers.1).2 + 1 ≤ _
  calc
    _ ≤ (history.length * 3 + 1) +
        (plonkColumnPrepareCostBudget costs node equal read omegaAccess canonicalRead compare
          actions history.length rowRead theta.2 stored +
        2048 * (plonkColumnRowCostBudget costs node equal read omegaAccess actions history.length rowRead
          witnessRead theta.2 beta.2 gamma.2 stored + 3) + 2 * 2048 * 2048 + 6) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add hp hc) 1
    _ = _ := by dsimp only [plonkStoredColumnCostBudget, rowRead]; ring

end Zcash.Snark.ZeroKnowledge
