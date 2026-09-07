import Zcash.Snark.ZeroKnowledge.KeygenCopyRows
import Zcash.Snark.ZeroKnowledge.PlonkCopyCells

/-!
# Compiler copies in the prover's packed cell type

The compiler's fifteen permutation columns are packed into chunks of widths seven,
seven, and one. Bounds proved from the compiler allow every raw copy to be decoded;
no entry is discarded. Re-encoding the packed list recovers the original ordered
stream, and its rows retain the compiler's sharper operation-footprint bound.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Halo2

/-- The three chunk widths specified by the pinned prover's fifteen-column permutation. -/
def plonkCopyChunkWidths (chunks : List (List (ColumnRef × ℕ))) : Prop :=
  ∀ c : Fin 3, (chunks.getD c.val []).length = min 7 (15 - c.val * 7)

/-- The compiler's global column and row coordinates of a packed prover cell. -/
def plonkCopyCellRaw {chunks : List (List (ColumnRef × ℕ))}
    (cell : PlonkCopyCell chunks) : ℕ × ℕ :=
  (cell.1.val * 7 + cell.2.2.val, cell.2.1.val)

/-- Pack an in-range compiler cell without changing its row or global column. -/
def plonkCopyCellOfFlat (chunks : List (List (ColumnRef × ℕ)))
    (hwidth : plonkCopyChunkWidths chunks) (cell : FlatCell 15 2042) : PlonkCopyCell chunks := by
  have hlt := cell.1.isLt
  have hchunk : cell.1.val / 7 < 3 := by omega
  have hcolumn : cell.1.val % 7 < (chunks.getD (cell.1.val / 7) []).length := by
    rw [hwidth ⟨cell.1.val / 7, hchunk⟩]
    change cell.1.val % 7 < min 7 (15 - cell.1.val / 7 * 7)
    exact lt_min (Nat.mod_lt _ (by decide)) (by omega)
  exact ⟨⟨cell.1.val / 7, hchunk⟩, cell.2, ⟨cell.1.val % 7, hcolumn⟩⟩

/-- Re-encoding a packed compiler cell returns its original coordinates. -/
theorem plonkCopyCellOfFlat_raw (chunks : List (List (ColumnRef × ℕ)))
    (hwidth : plonkCopyChunkWidths chunks) (cell : FlatCell 15 2042) :
    plonkCopyCellRaw (plonkCopyCellOfFlat chunks hwidth cell) = cell.pair := by
  apply Prod.ext
  · change cell.1.val / 7 * 7 + cell.1.val % 7 = cell.1.val
    omega
  · rfl

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- Compiler row and column bounds discharge every precondition of the finite copy decoder. -/
theorem plonkKeygenCopyRaw_bounds (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042)
    (tuple : ℕ × ℕ × ℕ × ℕ) (htuple : tuple ∈ plonkKeygenCopyRaw top) :
    tuple.1 < 15 ∧ tuple.2.1 < 2042 ∧ tuple.2.2.1 < 15 ∧ tuple.2.2.2 < 2042 := by
  have hcols := plonkKeygenCopyRaw_columns_lt top tuple htuple
  have hrow := plonkKeygenCopyRaw_rows_lt_usedRows top tuple htuple
  rw [hcolumns] at hcols
  exact ⟨hcols.1, hrow.1.trans_le hrows, hcols.2, hrow.2.trans_le hrows⟩

/-- All compiler copies decoded into fifteen columns and 2042 usable rows, in source order. -/
def plonkKeygenFlatCopies (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042) :
    List (FlatCell 15 2042 × FlatCell 15 2042) :=
  decodeCopies 15 2042 (plonkKeygenCopyRaw top) (plonkKeygenCopyRaw_bounds top hcolumns hrows)

/-- The compiler's complete ordered copy stream in the reference prover's packed cell type. -/
def plonkKeygenCopies (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks) :
    List (PlonkCopyCell chunks × PlonkCopyCell chunks) :=
  (plonkKeygenFlatCopies top hcolumns hrows).map fun pair =>
    (plonkCopyCellOfFlat chunks hwidth pair.1, plonkCopyCellOfFlat chunks hwidth pair.2)

/-- Packing and re-encoding preserves every raw compiler copy and its order. -/
theorem plonkKeygenCopies_encode (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks) :
    (plonkKeygenCopies top hcolumns hrows chunks hwidth).map
      (fun pair => ((plonkCopyCellRaw pair.1).1, (plonkCopyCellRaw pair.1).2,
        (plonkCopyCellRaw pair.2).1, (plonkCopyCellRaw pair.2).2)) = plonkKeygenCopyRaw top := by
  simpa only [plonkKeygenCopies, List.map_map, Function.comp_def, plonkCopyCellOfFlat_raw,
    plonkKeygenFlatCopies] using
      decodeCopies_map 15 2042 (plonkKeygenCopyRaw top) (plonkKeygenCopyRaw_bounds top hcolumns hrows)

/-- The packed copies preserve the compiler's operation-footprint bound on both endpoint rows. -/
theorem plonkKeygenCopies_rows_lt_usedRows (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks)
    (pair : PlonkCopyCell chunks × PlonkCopyCell chunks)
    (hpair : pair ∈ plonkKeygenCopies top hcolumns hrows chunks hwidth) :
    pair.1.2.1.val < Halo2.usedRows top.operations ∧ pair.2.2.1.val < Halo2.usedRows top.operations := by
  have hraw : ((plonkCopyCellRaw pair.1).1, (plonkCopyCellRaw pair.1).2,
      (plonkCopyCellRaw pair.2).1, (plonkCopyCellRaw pair.2).2) ∈ plonkKeygenCopyRaw top := by
    rw [← plonkKeygenCopies_encode top hcolumns hrows chunks hwidth]
    exact List.mem_map.mpr ⟨pair, hpair, rfl⟩
  exact plonkKeygenCopyRaw_rows_lt_usedRows top _ hraw

/-- A compiler footprint ending by row 2000 leaves that row untouched by every packed copy. -/
theorem plonkKeygenCopies_avoid_unused (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks)
    (hused : Halo2.usedRows top.operations ≤ 2000) :
    ∀ pair ∈ plonkKeygenCopies top hcolumns hrows chunks hwidth,
      pair.1.2.1.val ≠ 2000 ∧ pair.2.2.1.val ≠ 2000 := by
  intro pair hpair
  have hbound := plonkKeygenCopies_rows_lt_usedRows top hcolumns hrows chunks hwidth pair hpair
  omega

end Zcash.Snark.ZeroKnowledge
