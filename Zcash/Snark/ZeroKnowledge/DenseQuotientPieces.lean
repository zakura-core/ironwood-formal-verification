import Zcash.Snark.ZeroKnowledge.DenseDomainPieces

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Compute the actual domain quotient and materialize all eight original pieces. -/
@[irreducible] def densePlonkQuotientPiecesCosted (read add multiply omegaAccess : ℕ)
    (values : List Fp) : List (List Fp) × ℕ :=
  denseDomainPiecesCosted read add multiply omegaAccess 11 2048 8 values

/-- Cost erasure gives the eight original quotient pieces in their original order. -/
theorem densePlonkQuotientPiecesCosted_result (read add multiply omegaAccess : ℕ) (values : List Fp) :
    ((densePlonkQuotientPiecesCosted read add multiply omegaAccess values).1.map densePolynomial) =
      List.ofFn (plonkQuotientPieces (densePolynomial values)) := by
  unfold densePlonkQuotientPiecesCosted
  have h := denseDomainPiecesCosted_result read add multiply omegaAccess 11 2048 8 (by decide) values
  rewrite [show (2 ^ 11 : ℕ) = 2048 from by decide] at h
  exact h

/-- The materialized result contains all eight pieces. -/
theorem densePlonkQuotientPiecesCosted_length (read add multiply omegaAccess : ℕ) (values : List Fp) :
    (densePlonkQuotientPiecesCosted read add multiply omegaAccess values).1.length = 8 := by
  unfold densePlonkQuotientPiecesCosted
  exact denseDomainPiecesCosted_length read add multiply omegaAccess 11 2048 8 values

/-- Every piece contains the complete 2048-coefficient commitment vector. -/
theorem densePlonkQuotientPiecesCosted_width (read add multiply omegaAccess : ℕ) (values piece : List Fp)
    (hpiece : piece ∈ (densePlonkQuotientPiecesCosted read add multiply omegaAccess values).1) :
    piece.length = 2048 := by
  unfold densePlonkQuotientPiecesCosted at hpiece
  exact denseDomainPiecesCosted_width read add multiply omegaAccess 11 2048 8 values piece hpiece

/-- The pinned quotient-piece budget includes division and every coefficient read. -/
def densePlonkQuotientPiecesCostBudget (read add multiply omegaAccess valueCount : ℕ) : ℕ :=
  denseDomainPiecesCostBudget read add multiply omegaAccess 11 2048 8 valueCount

/-- Complete quotient-piece construction fits the explicit composite budget on every input. -/
theorem densePlonkQuotientPiecesCosted_cost_le (read add multiply omegaAccess : ℕ) (values : List Fp) :
    (densePlonkQuotientPiecesCosted read add multiply omegaAccess values).2 ≤
      densePlonkQuotientPiecesCostBudget read add multiply omegaAccess values.length := by
  unfold densePlonkQuotientPiecesCosted
  exact denseDomainPiecesCosted_cost_le read add multiply omegaAccess 11 2048 8 values

end Zcash.Snark.ZeroKnowledge
