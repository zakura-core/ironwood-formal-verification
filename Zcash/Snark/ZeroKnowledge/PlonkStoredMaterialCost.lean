import Zcash.Snark.ZeroKnowledge.PlonkCoinLayoutCost
import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnsCostBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Execute the complete private-material construction on the original pre-IPA tape. -/
def plonkStoredMaterialFromTapeCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (tape : List Fp) : (List (List Fp) × ((Fp × Fp) × List Fp)) × ℕ :=
  let coins := plonkPreIpaCoinsCosted read (fun (_ : PrivateColumnId actions) _ _ => 0) tape
  let columns := plonkStoredColumnsFromTapeCosted costs node equal read omegaAccess canonicalRead compare
    stored instances fixed sigma witness theta beta gamma coins.1.1
  ((columns.1, coins.1.2), coins.2 + columns.2 + 1)

/-- The stored computation is the entire original private state on the identical actual batched tape. -/
theorem plonkStoredMaterialFromTapeCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (ch : Challenges k Fp)
    (thetaRead betaRead gammaRead : ℕ)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches (plonkTotalColumnConstructor vk
      (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
        (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
      (fun a c r => (witness a c r).1) ch)) + 12) → Fp) :
    (plonkStoredMaterialFromTapeCosted costs node equal read omegaAccess canonicalRead compare
      (StoredPlonkKey.encode vk) instances fixed sigma witness (ch.theta, thetaRead) (ch.beta, betaRead)
      (ch.gamma, gammaRead) (List.ofFn tape)).1 =
      let material := plonkMaterialFromTape (plonkTotalColumnConstructor vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (fun a c r => (witness a c r).1) ch) [] tape
      (material.1.map List.ofFn, (material.2.1, List.ofFn material.2.2)) := by
  dsimp only [plonkStoredMaterialFromTapeCosted]
  rw [plonkPreIpaCoinsCosted_layout_result read _ _ tape]
  rw [plonkStoredColumnsFromTapeCosted_result costs node equal read omegaAccess canonicalRead compare
    vk instances fixed sigma witness ch thetaRead betaRead gammaRead]
  simp only [storedRow_getD_ofFn]
  rfl

/-- Enlarging the allowed tape size preserves the full stored-column budget. -/
theorem plonkStoredColumnsCostBudget_mono_tape (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare actions publicRowRead witnessRead thetaRead betaRead gammaRead : ℕ)
    (stored : StoredPlonkKey) {left right : ℕ} (h : left ≤ right) :
    plonkStoredColumnsCostBudget costs node equal read omegaAccess canonicalRead compare actions left
      publicRowRead witnessRead thetaRead betaRead gammaRead stored ≤
    plonkStoredColumnsCostBudget costs node equal read omegaAccess canonicalRead compare actions right
      publicRowRead witnessRead thetaRead betaRead gammaRead stored := by
  dsimp only [plonkStoredColumnsCostBudget]
  gcongr

end Zcash.Snark.ZeroKnowledge
