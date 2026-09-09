import Zcash.Snark.ZeroKnowledge.PlonkStoredMaterialCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Complete cost of decoding the actual tape and constructing all retained masked columns. -/
def plonkStoredMaterialCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare actions tapeSize publicRowRead witnessRead
      thetaRead betaRead gammaRead : ℕ) (stored : StoredPlonkKey) : ℕ :=
  plonkPreIpaCoinsCostBudget read actions tapeSize +
    plonkStoredColumnsCostBudget costs node equal read omegaAccess canonicalRead compare actions (126 * actions)
      publicRowRead witnessRead thetaRead betaRead gammaRead stored + 1

/-- Every private-material operation is counted, with no successful-sort or sampled-value premise. -/
theorem plonkStoredMaterialFromTapeCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (tape : List Fp) (publicRowRead witnessRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ publicRowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ publicRowRead) (hsigma : ∀ c r, (sigma c r).2 ≤ publicRowRead)
    (hwitness : ∀ a c r, (witness a c r).2 ≤ witnessRead) :
    (plonkStoredMaterialFromTapeCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma tape).2 ≤
      plonkStoredMaterialCostBudget costs node equal read omegaAccess canonicalRead compare actions tape.length
        publicRowRead witnessRead theta.2 beta.2 gamma.2 stored := by
  let layout := fun (_ : PrivateColumnId actions) (_ : ColumnHistory 2048) (_ : Fin 2048) => (0 : Fp)
  let coins := plonkPreIpaCoinsCosted read layout tape
  have hc := plonkPreIpaCoinsCosted_cost_le read layout tape
  have hn := plonkPreIpaCoinsCosted_rows_length_le read layout tape
  have hp := plonkStoredColumnsFromTapeCosted_cost_le costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma coins.1.1 publicRowRead witnessRead
    hinstances hfixed hsigma hwitness
  have hb := plonkStoredColumnsCostBudget_mono_tape costs node equal read omegaAccess canonicalRead compare
    actions publicRowRead witnessRead theta.2 beta.2 gamma.2 stored hn
  change coins.2 + (plonkStoredColumnsFromTapeCosted costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma coins.1.1).2 + 1 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add hc (hp.trans hb)) 1

end Zcash.Snark.ZeroKnowledge
