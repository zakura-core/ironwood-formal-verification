import Zcash.Snark.ZeroKnowledge.StoredBitTapeCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Common

/-- Consecutive fair bits supply a matrix of independent raw words, without rejection or field reduction. -/
def rawMatrixBitsEquiv (rows columns : ℕ) :
    (Fin ((rows * columns) * 512) → Bool) ≃ (Fin rows → Fin columns → Fin challengeDigestCard) :=
  (rawBitsTapeEquiv (rows * columns)).trans
    ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (Fin challengeDigestCard))).trans
      (Equiv.curry (Fin rows) (Fin columns) (Fin challengeDigestCard)))

theorem rawMatrixBitsEquiv_apply (rows columns : ℕ)
    (bits : Fin ((rows * columns) * 512) → Bool) (row : Fin rows) (column : Fin columns) :
    rawMatrixBitsEquiv rows columns bits row column =
      rawBitsTapeEquiv (rows * columns) bits (finProdFinEquiv (row, column)) := rfl

/-- The matrix's entire joint distribution is uniform; all rows and columns are independent. -/
theorem uniformRawMatrixBits (rows columns : ℕ) :
    (PMF.uniformOfFintype (Fin ((rows * columns) * 512) → Bool)).map (rawMatrixBitsEquiv rows columns) =
      PMF.uniformOfFintype (Fin rows → Fin columns → Fin challengeDigestCard) :=
  Zcash.map_uniformOfFintype_equiv _

/-- Materialize raw rows from a stored flat bit list, retaining packing, indexing, and list-access costs. -/
def storedRawMatrixCosted (rows columns read : ℕ) (bits : List Bool) :
    List (List (Fin challengeDigestCard)) × ℕ :=
  let raw := storedRawTapeCosted (rows * columns) read bits
  let matrix := ofFnCosted (fun row : Fin rows => ofFnCosted (fun column : Fin columns =>
    let value := getDListCosted read 0 raw.1 (finProdFinEquiv (row, column)).val
    (value.1, value.2 + 3)))
  (matrix.1, raw.2 + matrix.2 + 2)

/-- The stored rows preserve the exact consecutive little-endian word ordering. -/
theorem storedRawMatrixCosted_result (rows columns read : ℕ)
    (bits : Fin ((rows * columns) * 512) → Bool) :
    (storedRawMatrixCosted rows columns read (List.ofFn bits)).1 =
      List.ofFn (fun row => List.ofFn (rawMatrixBitsEquiv rows columns bits row)) := by
  simp only [storedRawMatrixCosted, ofFnCosted_result, storedRawTapeCosted_encode_result,
    getDListCosted_ofFn_result]
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext column
  exact (rawMatrixBitsEquiv_apply rows columns bits row column).symm

/-- Even a short stored input is decoded to the requested shape using the original zero default. -/
theorem storedRawMatrixCosted_shape (rows columns read : ℕ) (bits : List Bool) :
    (storedRawMatrixCosted rows columns read bits).1.length = rows ∧
      ∀ row ∈ (storedRawMatrixCosted rows columns read bits).1, row.length = columns := by
  simp only [storedRawMatrixCosted, ofFnCosted_result, List.length_ofFn, List.mem_ofFn]
  constructor
  · trivial
  · intro row h
    obtain ⟨index, rfl⟩ := h
    exact List.length_ofFn

/-- Every packing and matrix construction operation is included in this fixed envelope. -/
def storedRawMatrixCostBudget (rows columns read bitLength : ℕ) : ℕ :=
  let words := rows * columns
  words * (512 * (2 * bitLength + read + 4) + 264195) + words * words + 1 +
    rows * (columns * (2 * words + read + 5) + columns * columns + 2) + rows * rows + 3

theorem storedRawMatrixCosted_cost_le (rows columns read : ℕ) (bits : List Bool) :
    (storedRawMatrixCosted rows columns read bits).2 ≤ storedRawMatrixCostBudget rows columns read bits.length := by
  let raw := storedRawTapeCosted (rows * columns) read bits
  have hraw := storedRawTapeCosted_cost_le (rows * columns) read bits
  have hlen : raw.1.length = rows * columns := by simp only [raw, storedRawTapeCosted, ofFnCosted_result, List.length_ofFn]
  have helem (row : Fin rows) (column : Fin columns) :
      (getDListCosted read 0 raw.1 (finProdFinEquiv (row, column)).val).2 + 3 ≤ 2 * (rows * columns) + read + 4 := by
    have h := getDListCosted_cost_le read 0 raw.1 (finProdFinEquiv (row, column)).val
    rewrite [hlen] at h
    omega
  have hrow (row : Fin rows) := ofFnCosted_cost_le
    (fun column : Fin columns =>
      let value := getDListCosted read 0 raw.1 (finProdFinEquiv (row, column)).val
      (value.1, value.2 + 3)) _ (helem row)
  have hmatrix := ofFnCosted_cost_le _ _ hrow
  unfold storedRawMatrixCosted storedRawMatrixCostBudget
  dsimp only
  simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add hraw hmatrix) 2

end Zcash.Snark.ZeroKnowledge
