import Zcash.Snark.ZeroKnowledge.DenseDomainDivision
import Zcash.Snark.ZeroKnowledge.DenseCoefficientBlocks

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Divide by a complete domain and materialize the requested consecutive coefficient blocks. -/
@[irreducible] def denseDomainPiecesCosted (read add multiply omegaAccess k size count : ℕ)
    (values : List Fp) : List (List Fp) × ℕ :=
  let quotient := denseDomainQuotientCosted read add multiply omegaAccess k values
  let pieces := denseCoefficientBlocksCosted read size count quotient.1
  (pieces.1, quotient.2 + pieces.2 + 1)

/-- Erasure composes the original quotient and coefficient-block operations exactly. -/
theorem denseDomainPiecesCosted_result (read add multiply omegaAccess k size count : ℕ)
    (hk : k ≤ 32) (values : List Fp) :
    ((denseDomainPiecesCosted read add multiply omegaAccess k size count values).1.map densePolynomial) =
      List.ofFn (fun block : Fin count =>
        polynomialCoefficientBlock size block.val (domainQuotient (2 ^ k) (densePolynomial values))) := by
  rewrite [denseDomainPiecesCosted, denseCoefficientBlocksCosted_result,
    denseDomainQuotientCosted_result read add multiply omegaAccess k hk]
  rfl

/-- The complete collection has its declared block count. -/
theorem denseDomainPiecesCosted_length (read add multiply omegaAccess k size count : ℕ) (values : List Fp) :
    (denseDomainPiecesCosted read add multiply omegaAccess k size count values).1.length = count := by
  unfold denseDomainPiecesCosted
  dsimp only
  exact denseCoefficientBlocksCosted_length read size count
    (denseDomainQuotientCosted read add multiply omegaAccess k values).1

/-- Every block retains its declared coefficient capacity, even on zero and short inputs. -/
theorem denseDomainPiecesCosted_width (read add multiply omegaAccess k size count : ℕ)
    (values piece : List Fp)
    (hpiece : piece ∈ (denseDomainPiecesCosted read add multiply omegaAccess k size count values).1) :
    piece.length = size := by
  unfold denseDomainPiecesCosted at hpiece
  dsimp only at hpiece
  exact denseCoefficientBlocksCosted_width read size count
    (denseDomainQuotientCosted read add multiply omegaAccess k values).1 piece hpiece

/-- Explicit composition budget for the domain quotient and every stored coefficient block. -/
def denseDomainPiecesCostBudget (read add multiply omegaAccess k size count valueCount : ℕ) : ℕ :=
  ((2 ^ k) * (omegaAccess + (2 ^ k) * (multiply + 1) +
    valueCount * (read + add + multiply + 5) + read + 8) + (2 ^ k) * (2 ^ k) + 3) +
    (count * (size * (2 * valueCount + read + 4) + size * size + 2) + count * count + 1) + 1

/-- The full composition retains both preparation costs and all output construction. -/
theorem denseDomainPiecesCosted_cost_le (read add multiply omegaAccess k size count : ℕ) (values : List Fp) :
    (denseDomainPiecesCosted read add multiply omegaAccess k size count values).2 ≤
      denseDomainPiecesCostBudget read add multiply omegaAccess k size count values.length := by
  have hq := denseDomainQuotientCosted_cost_le read add multiply omegaAccess k values
  have hp := denseCoefficientBlocksCosted_cost_le read size count
    (denseDomainQuotientCosted read add multiply omegaAccess k values).1
  rewrite [denseDomainQuotientCosted_length] at hp
  unfold denseDomainPiecesCosted
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add hq hp) 1

end Zcash.Snark.ZeroKnowledge
