import Zcash.Snark.ZeroKnowledge.PlonkExpressionRows
import Zcash.Snark.ZeroKnowledge.PlonkCopyCells

/-!
# Exact query values in the prover's packed permutation cells
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- A permutation cell reads its exact query from the actual polynomial proof. -/
theorem plonkCopyCellPair_value {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (action : Fin actions) (chunks : List (List (ColumnRef × ℕ)))
    (cell : PlonkCopyCell chunks) :
    (plonkCopyCellPair pub rows action chunks cell).1 =
      (plonkCopyCellEntry cell).1.resolve
        (plonkInstanceRowValues pub action (cell.2.1.castLE (by decide)))
        (plonkAdviceRowValues rows action (cell.2.1.castLE (by decide)))
        (plonkFixedRowValues pub (cell.2.1.castLE (by decide))) := by
  have hj : cell.2.2.val <
      (plonkPermutationFactorRows pub rows action chunks cell.1.val cell.2.1.val).length := by
    rw [plonkPermutationFactorRows_length]
    exact cell.2.2.isLt
  unfold plonkCopyCellPair plonkCopyCellEntry
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ cell.2.2.isLt]
  simp only [plonkPermutationFactorRows, plonkPermutationPairPolynomials, List.getElem_map]
  generalize (chunks.getD cell.1.val [])[cell.2.2.val].1 = reference
  cases reference with
  | advice index => exact plonkPolynomialClaimProof_adviceRowValues (k := 0) (G := Fp) pub rows action (cell.2.1.castLE (by decide)) index
  | fixed index => exact plonkPolynomialClaimProof_fixedRowValues (k := 0) (G := Fp) pub rows (cell.2.1.castLE (by decide)) index
  | «instance» index => exact plonkPolynomialClaimProof_instanceRowValues (k := 0) (G := Fp) pub rows action (cell.2.1.castLE (by decide)) index

end Zcash.Snark.ZeroKnowledge
