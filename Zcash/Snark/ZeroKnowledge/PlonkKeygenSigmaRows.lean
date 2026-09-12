import Zcash.Snark.ZeroKnowledge.CopyReplayTransport
import Zcash.Snark.ZeroKnowledge.PlonkKeygenCopies

/-!
# Compiler sigma rows are the names of replayed packed cells

The usable packed cells embed injectively into the compiler's full rectangular
permutation table. Transporting the ordered copy replay through that embedding
identifies the compiler's actual sigma-row computation with the names used by the
reference prover. This uses the existing array/union-find assembly theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp deltaFp omegaOf)
open Halo2

/-- Embed a usable packed cell into the compiler's full-domain rectangular table. -/
def plonkCopyCellToFull (columns : ℕ) (hcolumns : columns = 15)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks)
    (cell : PlonkCopyCell chunks) : FlatCell columns 2048 := by
  refine (⟨cell.1.val * 7 + cell.2.2.val, ?_⟩, cell.2.1.castLE (by decide))
  rw [hcolumns]
  have hlocal := cell.2.2.isLt.trans_le (hwidth cell.1).le
  omega

/-- The full-domain embedding keeps both numeric coordinates. -/
theorem plonkCopyCellToFull_pair (columns : ℕ) (hcolumns : columns = 15)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks)
    (cell : PlonkCopyCell chunks) :
    (plonkCopyCellToFull columns hcolumns chunks hwidth cell).pair = plonkCopyCellRaw cell := rfl

/-- Distinct usable packed cells have distinct full-domain compiler coordinates. -/
theorem plonkCopyCellToFull_injective (columns : ℕ) (hcolumns : columns = 15)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks) :
    Function.Injective (plonkCopyCellToFull columns hcolumns chunks hwidth) := by
  intro left right heq
  have hcoords := congrArg FlatCell.pair heq
  simp only [plonkCopyCellToFull_pair] at hcoords
  apply flattenPermutationChunkCell_injective (m := 2042) (chunkLen := 7)
    (fun c hc => (hwidth ⟨c, hc⟩).le.trans (min_le_left _ _))
  exact Prod.ext (Fin.ext (congrArg Prod.snd hcoords)) (Fin.ext (congrArg Prod.fst hcoords))

/-- Widening all packed copies preserves their complete raw tuple stream. -/
theorem plonkCopyCellToFull_copies_encode (columns : ℕ) (hcolumns : columns = 15)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks)
    (copies : List (PlonkCopyCell chunks × PlonkCopyCell chunks)) :
    (copies.map fun pair =>
      (plonkCopyCellToFull columns hcolumns chunks hwidth pair.1,
        plonkCopyCellToFull columns hcolumns chunks hwidth pair.2)).map
      (fun pair => (pair.1.pair.1, pair.1.pair.2, pair.2.pair.1, pair.2.pair.2)) =
      copies.map (fun pair => ((plonkCopyCellRaw pair.1).1, (plonkCopyCellRaw pair.1).2,
        (plonkCopyCellRaw pair.2).1, (plonkCopyCellRaw pair.2).2)) := by
  simp only [List.map_map, Function.comp_def, plonkCopyCellToFull_pair]

/-- The compiler's sigma table reads the exact image under packed copy replay. -/
theorem plonkCompilerSigmaRow_eq_replay (cs : ConstraintSystem Fp) (operations : Operations Fp)
    (hcolumns : (Keygen.permColsOf cs).length = 15)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks)
    (copies : List (PlonkCopyCell chunks × PlonkCopyCell chunks))
    (hcopies : Layout.V1.copyList (Keygen.permColsOf cs) (FloorPlanner.V1.starts operations)
      operations (Keygen.constantCopyEntries cs operations) =
      copies.map (fun pair => ((plonkCopyCellRaw pair.1).1, (plonkCopyCellRaw pair.1).2,
        (plonkCopyCellRaw pair.2).1, (plonkCopyCellRaw pair.2).2)))
    (cell : PlonkCopyCell chunks) :
    ((Keygen.permPolysOf 11 cs operations).getD (plonkCopyCellRaw cell).1 []).getD cell.2.1.val 0 =
      deltaFp ^ (plonkCopyCellRaw (replayKeygenPermutation copies cell)).1 *
        omegaOf 11 ^ (plonkCopyCellRaw (replayKeygenPermutation copies cell)).2 := by
  let encode := plonkCopyCellToFull (Keygen.permColsOf cs).length hcolumns chunks hwidth
  have hraw := hcopies.trans
    (plonkCopyCellToFull_copies_encode (Keygen.permColsOf cs).length hcolumns chunks hwidth copies).symm
  have hentry := Layout.Asm.permPolysOf_getD_eq (k := 11) cs operations
    (copies.map fun pair => (encode pair.1, encode pair.2)) hraw (encode cell).1 (encode cell).2
  have htransport := replayKeygenPermutation_map_apply encode
    (plonkCopyCellToFull_injective (Keygen.permColsOf cs).length hcolumns chunks hwidth) copies cell
  have hpair : ((encode cell).1, (encode cell).2) = encode cell := by cases encode cell; rfl
  rw [hpair, ← htransport] at hentry
  exact hentry

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The compiler's sigma table, restricted to the pinned fifteen columns and 2048 rows. -/
def plonkKeygenSigmaRows (top : TopLevelCircuit Fp Config PublicInput) : Fin 15 → Fin 2048 → Fp :=
  fun column row => ((Keygen.permPolysOf 11 top.constraintSystem top.operations).getD column.val []).getD row.val 0

/-- Every usable compiler sigma entry is the name of the image under its computed packed copy list. -/
theorem plonkKeygenSigmaRows_eq_replay (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks)
    (cell : PlonkCopyCell chunks) :
    ((Keygen.permPolysOf 11 top.constraintSystem top.operations).getD (plonkCopyCellRaw cell).1 []).getD
        cell.2.1.val 0 =
      deltaFp ^ (plonkCopyCellRaw
        (replayKeygenPermutation (plonkKeygenCopies top hcolumns hrows chunks hwidth) cell)).1 *
        omegaOf 11 ^ (plonkCopyCellRaw
          (replayKeygenPermutation (plonkKeygenCopies top hcolumns hrows chunks hwidth) cell)).2 := by
  have hcount : (Keygen.permColsOf top.constraintSystem).length = 15 := by
    simpa only [Keygen.permColsOf, List.length_map, TopLevelCircuit.permutationColumnCount,
      TopLevelCircuit.permutationColumns] using hcolumns
  exact plonkCompilerSigmaRow_eq_replay top.constraintSystem top.operations hcount chunks hwidth
    (plonkKeygenCopies top hcolumns hrows chunks hwidth)
    (plonkKeygenCopies_encode top hcolumns hrows chunks hwidth).symm cell

end Zcash.Snark.ZeroKnowledge
