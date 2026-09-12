import Zcash.Snark.ZeroKnowledge.PlonkStoredMaterialCostBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Even a truncated tape produces no more than the original commitment-blind capacity. -/
theorem plonkPreIpaCoinsCosted_blinds_length_le {actions : ℕ} (read : ℕ)
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) (tape : List Fp) :
    (plonkPreIpaCoinsCosted read construct tape).1.2.2.length ≤ 22 * actions + 10 := by
  let first := splitListCosted read (148 * actions) tape
  let columns := plonkBatchedColumnCoinsCosted read construct first.1.1
  let coefficients := splitListCosted read 2 first.1.2
  have hn : columns.1.2.length ≤ 22 * actions := by
    dsimp only [columns, plonkBatchedColumnCoinsCosted]
    rewrite [batchedColumnTapeListsCosted_result, plonkColumnBatchesCosted_result]
    have h := batchedColumnTapeLists_blinds_length_le (plonkColumnBatches construct) first.1.1
    simpa only [plonkColumnBatches_flatten, plonkColumnSteps_length] using h
  have he : (splitListCosted read 10 coefficients.1.2).1.1.length ≤ 10 := by
    rewrite [splitListCosted_result]
    exact List.length_take_le _ _
  change (appendListCosted columns.1.2 (splitListCosted read 10 coefficients.1.2).1.1).1.length ≤ _
  rewrite [appendListCosted_result, List.length_append]
  omega

/-- All private columns are present, each has 2048 rows, and all stored blinds fit the original vector. -/
theorem plonkStoredMaterialFromTapeCosted_dimensions (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (key : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ) (tape : List Fp) :
    let material := (plonkStoredMaterialFromTapeCosted costs node equal read omegaAccess canonicalRead compare
      key instances fixed sigma witness theta beta gamma tape).1
    material.1.length = 22 * actions ∧ (∀ column ∈ material.1, column.length = 2048) ∧
      material.2.2.length ≤ 22 * actions + 10 := by
  let coins := plonkPreIpaCoinsCosted read (fun (_ : PrivateColumnId actions) _ _ => 0) tape
  exact ⟨plonkStoredColumnsFromTapeCosted_length costs node equal read omegaAccess canonicalRead compare
    key instances fixed sigma witness theta beta gamma coins.1.1,
    plonkStoredColumnsFromTapeCosted_width costs node equal read omegaAccess canonicalRead compare
    key instances fixed sigma witness theta beta gamma coins.1.1,
    plonkPreIpaCoinsCosted_blinds_length_le read _ tape⟩

end Zcash.Snark.ZeroKnowledge
