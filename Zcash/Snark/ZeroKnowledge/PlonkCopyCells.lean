import Zcash.Snark.ZeroKnowledge.PlonkPermutationMasking
import Zcash.Snark.ZeroKnowledge.CopyProducts

/-!+# Typed cells for the concrete packed copy argument

The finite cell type has exactly the three actual chunks, their public widths, and
the 2042 usable rows. Its values are read from the computed factor lists, while its
identity names and sigma labels depend only on public data. Reindexing these cells
recovers the numerator and denominator loops used by the reference product scans.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Finset

/-- A usable cell in one of the three packed permutation chunks. -/
abbrev PlonkCopyCell (chunks : List (List (ColumnRef × ℕ))) :=
  ChunkCell 3 2042 (fun c => (chunks.getD c []).length)

/-- The cell's resolved value and sigma label in the actual factor list. -/
def plonkCopyCellPair {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (a : Fin actions) (chunks : List (List (ColumnRef × ℕ)))
    (cell : PlonkCopyCell chunks) : Fp × Fp :=
  (plonkPermutationFactorRows pub rows a chunks cell.1.val cell.2.1.val).getD cell.2.2.val (0, 0)

/-- The public identity label used by the numerator, preserving the key's chunk stride. -/
def plonkCopyCellName {chunks : List (List (ColumnRef × ℕ))} (delta : Fp) (stride : ℕ)
    (cell : PlonkCopyCell chunks) : Fp :=
  omegaOf 11 ^ cell.2.1.val * delta ^ (cell.1.val * stride) * delta ^ cell.2.2.val

/-- The public query and sigma indices at a typed packed cell. -/
def plonkCopyCellEntry {chunks : List (List (ColumnRef × ℕ))} (cell : PlonkCopyCell chunks) :
    ColumnRef × ℕ :=
  (chunks.getD cell.1.val []).getD cell.2.2.val (.advice 0, 0)

/-- The public sigma polynomial evaluated at the cell's usable row. -/
def plonkCopyCellSigma {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    {chunks : List (List (ColumnRef × ℕ))} (cell : PlonkCopyCell chunks) : Fp :=
  (finFn pub.sigma (plonkCopyCellEntry cell).2).eval (omegaOf 11 ^ cell.2.1.val)

/-- The second factor coordinate is precisely the public sigma label. -/
theorem plonkCopyCellPair_sigma {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (a : Fin actions) (chunks : List (List (ColumnRef × ℕ)))
    (cell : PlonkCopyCell chunks) :
    (plonkCopyCellPair pub rows a chunks cell).2 = plonkCopyCellSigma pub cell := by
  have hj : cell.2.2.val <
      (plonkPermutationFactorRows pub rows a chunks cell.1.val cell.2.1.val).length := by
    rw [plonkPermutationFactorRows_length]
    exact cell.2.2.isLt
  unfold plonkCopyCellPair plonkCopyCellSigma plonkCopyCellEntry
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ cell.2.2.isLt]
  simp only [plonkPermutationFactorRows, plonkPermutationPairPolynomials, List.getElem_map]
  rfl

/-- All computed usable cell pairs equal their original unmasked counterparts on every tape. -/
theorem plonkCopyCellPair_masked {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp)
    (hqueries : plonkPermutationQueriesUnrotated vk.permutationChunks = true)
    (a : Fin actions) (cell : PlonkCopyCell vk.permutationChunks) :
    plonkCopyCellPair pub (plonkTotalColumnRows vk pub witness ch tape) a vk.permutationChunks cell =
      plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks cell := by
  exact congrArg (fun pairs : List (Fp × Fp) => pairs.getD cell.2.2.val (0, 0))
    (plonkPermutationFactorRows_masked vk pub witness ch tape hqueries a cell.1.val
      (cell.2.1.castLE (by decide)) cell.2.1.isLt)

/-- The actual numerator loop is the product over all named typed cells. -/
theorem plonkPermutationNumerator_prod_cells {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (a : Fin actions) (chunks : List (List (ColumnRef × ℕ)))
    (beta gamma delta : Fp) (stride : ℕ) :
    (∏ c ∈ range 3, ∏ i ∈ range 2042,
      permutationRowNumerator (plonkPermutationFactorRows pub rows a chunks)
        beta gamma (omegaOf 11) delta stride c i) =
      ∏ cell : PlonkCopyCell chunks,
        ((plonkCopyCellPair pub rows a chunks cell).1 + beta * plonkCopyCellName delta stride cell + gamma) := by
  simp only [permutationRowNumerator, plonkPermutationFactorRows_length]
  simpa only [plonkCopyCellPair, plonkCopyCellName, mul_assoc] using
    (prod_chunk_cells 3 2042 (fun c => (chunks.getD c []).length) (fun c i j =>
      ((plonkPermutationFactorRows pub rows a chunks c i).getD j (0, 0)).1 +
        beta * omegaOf 11 ^ i * delta ^ (c * stride) * delta ^ j + gamma)).symm

/-- The actual denominator loop is the product over all sigma-labelled typed cells. -/
theorem plonkPermutationDenominator_prod_cells {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (a : Fin actions) (chunks : List (List (ColumnRef × ℕ)))
    (beta gamma : Fp) :
    (∏ c ∈ range 3, ∏ i ∈ range 2042,
      permutationRowDenominator (plonkPermutationFactorRows pub rows a chunks) beta gamma c i) =
      ∏ cell : PlonkCopyCell chunks,
        ((plonkCopyCellPair pub rows a chunks cell).1 + beta * (plonkCopyCellPair pub rows a chunks cell).2 + gamma) := by
  simp only [permutationRowDenominator, plonkPermutationFactorRows_length]
  exact (prod_chunk_cells 3 2042 (fun c => (chunks.getD c []).length) (fun c i j =>
    ((plonkPermutationFactorRows pub rows a chunks c i).getD j (0, 0)).1 +
      beta * ((plonkPermutationFactorRows pub rows a chunks c i).getD j (0, 0)).2 + gamma)).symm

end Zcash.Snark.ZeroKnowledge
