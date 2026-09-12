import Zcash.Snark.ZeroKnowledge.LookupPolynomialRows

/-!
# The honest proof's lookup columns use the checked polynomial layout

The lookup records in the actual `ProofString` and constraint model are the running
product, permuted input, and permuted table polynomials with the precise next/previous
rotations used by the row-to-polynomial correctness theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial

/-- Query zero is the original column polynomial. -/
theorem plonkRotatedColumn_zero {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) :
    plonkRotatedColumn rows id 0 = privateColumnPolynomial rows id := by
  change (privateColumnPolynomial rows id).comp (C 1 * X) = privateColumnPolynomial rows id
  apply toPoly_injective
  rw [toPoly_comp, toPoly_mul, C_toPoly, X_toPoly, Polynomial.C_1, _root_.one_mul, Polynomial.comp_X]

/-- The proof string's lookup record is exactly the checked rotated polynomial record. -/
theorem plonkPolynomialClaimProof_lookupEvals {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048) (a : Fin actions) (l : Fin 3) :
    (plonkPolynomialClaimProof (k := k) (G := G) pub rows).lookupEvals a l =
      lookupEvalPolys (omegaOf 11) (privateColumnPolynomial rows (.lookupProduct a l))
        (privateColumnPolynomial rows (.lookupInput a l))
        (privateColumnPolynomial rows (.lookupTable a l)) := by
  simp only [plonkPolynomialClaimProof, plonkClaimProof, plonkProofString,
    plonkRotatedColumn_zero]
  rfl

/-- Each Action's three lookup entries use that same record and the key's actual expressions. -/
theorem plonkConstraintModel_lookups {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) (a : Fin actions) :
    (plonkConstraintModel vk pub ch rows).lookups a =
      List.ofFn (fun l : Fin 3 =>
        (lookupEvalPolys (omegaOf 11) (privateColumnPolynomial rows (.lookupProduct a l))
          (privateColumnPolynomial rows (.lookupInput a l))
          (privateColumnPolynomial rows (.lookupTable a l)), vk.lookupInputExprs l, vk.lookupTableExprs l)) := by
  simp only [plonkConstraintModel, plonkPolynomialClaimProof_lookupEvals]
  rfl

end Zcash.Snark.ZeroKnowledge
