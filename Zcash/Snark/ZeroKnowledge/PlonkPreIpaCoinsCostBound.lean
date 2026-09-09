import Zcash.Snark.ZeroKnowledge.PlonkPreIpaCoinsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Complete deterministic budget for the actual pre-IPA coin decoder. -/
def plonkPreIpaCoinsCostBudget (read actions tapeSize : ℕ) : ℕ :=
  (1984 * actions * actions + 280 * actions + 12 +
    (10 * actions) * (2 * tapeSize * (read + 3) + 4 * (22 * actions) + 16) + 2) +
      3 * tapeSize * (read + 2) + 4 * tapeSize + 2 * read + 22 * actions + 20

/-- The complete decoder produces at most the original 126 row-mask samples per Action. -/
theorem plonkPreIpaCoinsCosted_rows_length_le {actions : ℕ} (read : ℕ)
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) (tape : List Fp) :
    (plonkPreIpaCoinsCosted read construct tape).1.1.length ≤ 126 * actions := by
  dsimp only [plonkPreIpaCoinsCosted, plonkBatchedColumnCoinsCosted]
  rw [batchedColumnTapeListsCosted_result, plonkColumnBatchesCosted_result]
  have h := batchedColumnTapeLists_rows_length_le (plonkColumnBatches construct)
    (splitListCosted read (148 * actions) tape).1.1
  simpa only [plonkColumnBatches_flatten, plonkColumnSteps_row_samples] using h

/-- Every metadata, tape, coefficient, and blind operation is included, even for truncated tapes. -/
theorem plonkPreIpaCoinsCosted_cost_le {actions : ℕ} (read : ℕ)
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) (tape : List Fp) :
    (plonkPreIpaCoinsCosted read construct tape).2 ≤ plonkPreIpaCoinsCostBudget read actions tape.length := by
  let first := splitListCosted read (148 * actions) tape
  let columns := plonkBatchedColumnCoinsCosted read construct first.1.1
  let coefficients := splitListCosted read 2 first.1.2
  let extra := splitListCosted read 10 coefficients.1.2
  have hf := splitListCosted_lengths_le read (148 * actions) tape
  have hc := splitListCosted_lengths_le read 2 first.1.2
  have hfirst : first.2 ≤ tape.length * (read + 2) + 1 := splitListCosted_cost_le _ _ _
  have hcoeff : coefficients.2 ≤ tape.length * (read + 2) + 1 :=
    (splitListCosted_cost_le _ _ _).trans (by gcongr; exact hf.2)
  have hextra : extra.2 ≤ tape.length * (read + 2) + 1 :=
    (splitListCosted_cost_le _ _ _).trans (by gcongr; exact hc.2.trans hf.2)
  have hcolumns : columns.2 ≤ 1984 * actions * actions + 280 * actions + 12 +
      (10 * actions) * (2 * tape.length * (read + 3) + 4 * (22 * actions) + 16) + 2 :=
    (plonkBatchedColumnCoinsCosted_cost_le read construct first.1.1).trans (by gcongr; exact hf.1)
  have hc0 : (getDListCosted read (0 : Fp) coefficients.1.1 0).2 ≤ 2 * tape.length + read + 1 :=
    (getDListCosted_cost_le _ _ _ _).trans (by gcongr; exact hc.1.trans hf.2)
  have hc1 : (getDListCosted read (0 : Fp) coefficients.1.1 1).2 ≤ 2 * tape.length + read + 1 :=
    (getDListCosted_cost_le _ _ _ _).trans (by gcongr; exact hc.1.trans hf.2)
  have hn : columns.1.2.length ≤ 22 * actions := by
    dsimp only [columns, plonkBatchedColumnCoinsCosted]
    rw [batchedColumnTapeListsCosted_result, plonkColumnBatchesCosted_result]
    have h := batchedColumnTapeLists_blinds_length_le (plonkColumnBatches construct) first.1.1
    simpa only [plonkColumnBatches_flatten, plonkColumnSteps_length] using h
  have hblinds : (appendListCosted columns.1.2 extra.1.1).2 ≤ 22 * actions + 1 := by
    rw [appendListCosted_cost]
    exact Nat.add_le_add_right hn 1
  change first.2 + columns.2 + coefficients.2 + extra.2 +
    (getDListCosted read (0 : Fp) coefficients.1.1 0).2 +
    (getDListCosted read (0 : Fp) coefficients.1.1 1).2 +
    (appendListCosted columns.1.2 extra.1.1).2 + 8 ≤ _
  dsimp only [plonkPreIpaCoinsCostBudget]
  nlinarith

end Zcash.Snark.ZeroKnowledge
