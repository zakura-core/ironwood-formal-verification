import Zcash.Snark.ZeroKnowledge.PrivateColumnBatchesCost
import Zcash.Snark.ZeroKnowledge.BatchedTapeCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Install the original mask boundaries and row callbacks in the materialized source batches. -/
def plonkColumnBatchesCosted {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) :
    List (List (ColumnStep 2048)) × ℕ :=
  let ids := privateColumnBatchesCosted actions
  let batches := mapListCosted (fun block =>
    mapListCosted (fun id => (ColumnStep.mk id.firstMasked (construct id), 8)) block) ids.1
  (batches.1, ids.2 + batches.2 + 1)

/-- Schedule preparation changes neither batch boundaries nor callbacks. -/
theorem plonkColumnBatchesCosted_result {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) :
    (plonkColumnBatchesCosted construct).1 = plonkColumnBatches construct := by
  simp only [plonkColumnBatchesCosted, mapListCosted_result, privateColumnBatchesCosted_result,
    plonkColumnBatches]

/-- The stored source contains exactly ten batches per Action. -/
theorem plonkColumnBatchesCosted_length {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) :
    (plonkColumnBatchesCosted construct).1.length = 10 * actions := by
  rw [plonkColumnBatchesCosted_result, plonkColumnBatches, List.length_map, privateColumnBatches_length]

/-- Every batch fits in the source's complete twenty-two-column schedule. -/
theorem plonkColumnBatchesCosted_block_length {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp)
    (block : List (ColumnStep 2048)) (hb : block ∈ (plonkColumnBatchesCosted construct).1) :
    block.length ≤ 22 * actions := by
  have h := (List.sublist_flatten_of_mem hb).length_le
  rwa [plonkColumnBatchesCosted_result, plonkColumnBatches_flatten, plonkColumnSteps_length] at h

/-- Complete batch preparation includes the original identifier construction and every stored callback. -/
theorem plonkColumnBatchesCosted_cost_le {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) :
    (plonkColumnBatchesCosted construct).2 ≤ 1984 * actions * actions + 280 * actions + 12 := by
  let ids := privateColumnBatchesCosted actions
  have hi := privateColumnBatchesCosted_cost_le actions
  have hn : ids.1.length = 10 * actions := by
    rw [privateColumnBatchesCosted_result, privateColumnBatches_length]
  have hb (block : List (PrivateColumnId actions)) (hblock : block ∈ ids.1) : block.length ≤ 22 * actions := by
    have h := (List.sublist_flatten_of_mem hblock).length_le
    rwa [privateColumnBatchesCosted_result, privateColumnBatches_flatten, privateColumnOrder_length] at h
  have hm := mapListCosted_cost_le (fun block =>
      mapListCosted (fun id => (ColumnStep.mk id.firstMasked (construct id), 8)) block) ids.1
    ((22 * actions) * 9 + 1) (by
      intro block hblock
      have h := mapListCosted_cost_le (fun id : PrivateColumnId actions =>
        (ColumnStep.mk id.firstMasked (construct id), 8)) block 8 (by simp)
      exact h.trans (by gcongr; exact hb block hblock))
  rw [hn] at hm
  change ids.2 + (mapListCosted (fun block =>
    mapListCosted (fun id => (ColumnStep.mk id.firstMasked (construct id), 8)) block) ids.1).2 + 1 ≤ _
  nlinarith

/-- Decode the actual private-column batches, including full schedule preparation. -/
def plonkBatchedColumnCoinsCosted {actions : ℕ} (read : ℕ)
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) (tape : List Fp) :
    (List Fp × List Fp) × ℕ :=
  let batches := plonkColumnBatchesCosted construct
  let coins := batchedColumnTapeListsCosted read batches.1 tape
  (coins.1, batches.2 + coins.2 + 1)

/-- This complete decoder has exactly the original batched column-coin semantics. -/
theorem plonkBatchedColumnCoinsCosted_result {actions : ℕ} (read : ℕ)
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches construct)) → Fp) :
    (plonkBatchedColumnCoinsCosted read construct (List.ofFn tape)).1 =
      (List.ofFn (columnCoinEquiv (plonkColumnBatches construct).flatten
        (batchedToColumnTape (plonkColumnBatches construct) tape)).1,
       List.ofFn (columnCoinEquiv (plonkColumnBatches construct).flatten
        (batchedToColumnTape (plonkColumnBatches construct) tape)).2) := by
  simp only [plonkBatchedColumnCoinsCosted, plonkColumnBatchesCosted_result]
  exact batchedColumnTapeListsCosted_source _ _ _

/-- The actual decoder's entire budget depends only on Action count, tape size, and the read price. -/
theorem plonkBatchedColumnCoinsCosted_cost_le {actions : ℕ} (read : ℕ)
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) (tape : List Fp) :
    (plonkBatchedColumnCoinsCosted read construct tape).2 ≤
      1984 * actions * actions + 280 * actions + 12 +
        (10 * actions) * (2 * tape.length * (read + 3) + 4 * (22 * actions) + 16) + 2 := by
  have hp := plonkColumnBatchesCosted_cost_le construct
  have hd := batchedColumnTapeListsCosted_cost_le read (plonkColumnBatchesCosted construct).1 tape
    (22 * actions) tape.length (plonkColumnBatchesCosted_block_length construct) le_rfl
  rw [plonkColumnBatchesCosted_length] at hd
  dsimp only [plonkBatchedColumnCoinsCosted]
  omega

end Zcash.Snark.ZeroKnowledge
