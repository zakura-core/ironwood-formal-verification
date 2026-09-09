import Zcash.Snark.ZeroKnowledge.PlonkNumeratorCoefficientsBound
import Zcash.Snark.ZeroKnowledge.DenseQuotientPieces

set_option maxHeartbeats 100000

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark CompPoly

attribute [local irreducible] plonkNumeratorCoefficientsCosted

/-- Construct the actual numerator from the original rows, divide it, and store all eight quotient pieces. -/
@[irreducible] def plonkQuotientPiecesFromRowsCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) : List (List Fp) × ℕ :=
  let numerator := plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows
  let pieces := densePlonkQuotientPiecesCosted read costs.add costs.multiply omegaAccess numerator.1
  (pieces.1, numerator.2 + pieces.2 + 1)

/-- Erasure gives precisely the reference prover's quotient pieces for the supplied row state. -/
theorem plonkQuotientPiecesFromRowsCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    ((plonkQuotientPiecesFromRowsCosted costs node equal read omegaAccess (StoredPlonkKey.encode vk)
      ch instances fixed sigma rows).1.map densePolynomial) =
      List.ofFn (plonkQuotientPieces (plonkConstraintNumerator vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (Challenges.eraseCosts ch) (rows.map (fun column row => (column row).1)))) := by
  unfold plonkQuotientPiecesFromRowsCosted
  change ((densePlonkQuotientPiecesCosted read costs.add costs.multiply omegaAccess
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess (StoredPlonkKey.encode vk)
      ch instances fixed sigma rows).1).1.map densePolynomial) = _
  exact (densePlonkQuotientPiecesCosted_result read costs.add costs.multiply omegaAccess
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess (StoredPlonkKey.encode vk)
      ch instances fixed sigma rows).1).trans
    (congrArg (fun numerator => List.ofFn (plonkQuotientPieces numerator))
      (plonkNumeratorCoefficientsCosted_result costs node equal read omegaAccess vk ch instances fixed sigma rows
        profile homega hn hblind))

/-- Every input produces the complete eight-piece storage layout. -/
theorem plonkQuotientPiecesFromRowsCosted_length (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) :
    (plonkQuotientPiecesFromRowsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).1.length = 8 := by
  unfold plonkQuotientPiecesFromRowsCosted
  change (densePlonkQuotientPiecesCosted read costs.add costs.multiply omegaAccess
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).1).1.length = 8
  exact densePlonkQuotientPiecesCosted_length read costs.add costs.multiply omegaAccess
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).1

/-- Every returned piece has the full commitment-vector width. -/
theorem plonkQuotientPiecesFromRowsCosted_width (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions k : ℕ} (key : StoredPlonkKey) (ch : Challenges k (Fp × ℕ))
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (piece : List Fp)
    (hpiece : piece ∈ (plonkQuotientPiecesFromRowsCosted costs node equal read omegaAccess key ch
      instances fixed sigma rows).1) : piece.length = 2048 := by
  unfold plonkQuotientPiecesFromRowsCosted at hpiece
  change piece ∈ (densePlonkQuotientPiecesCosted read costs.add costs.multiply omegaAccess
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).1).1 at hpiece
  exact densePlonkQuotientPiecesCosted_width read costs.add costs.multiply omegaAccess
    (plonkNumeratorCoefficientsCosted costs node equal read omegaAccess key ch instances fixed sigma rows).1 piece hpiece

end Zcash.Snark.ZeroKnowledge
