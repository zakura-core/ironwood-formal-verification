import Zcash.Snark.ZeroKnowledge.DenseRowPolynomial
import Zcash.Snark.ZeroKnowledge.DomainCertificate

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark CompPoly

/-- Interpolating every domain evaluation recovers any polynomial below the domain degree. -/
theorem rowPolynomial_evaluations (k : ℕ) (hk : k ≤ 32) (poly : CPoly)
    (hdegree : poly.natDegree < 2 ^ k) :
    rowPolynomial (omegaOf k) (fun index : Fin (2 ^ k) => poly.eval (omegaOf k ^ index.val)) = poly := by
  apply CPolynomial.toPoly_injective
  rw [toPoly_rowPolynomial]
  simp only [CPolynomial.eval_toPoly]
  symm
  apply Lagrange.eq_interpolate (omegaOf_rows_injective k hk).injOn
  have h : poly.toPoly.natDegree < 2 ^ k := by
    simpa only [CPolynomial.natDegree_toPoly] using hdegree
  simp only [Finset.card_univ, Fintype.card_fin]
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h)

/-- A nonzero coset shift can be undone by the inverse variable rotation. -/
theorem polynomial_comp_inverse_rotation (poly : CPoly) (factor : Fp) (hfactor : factor ≠ 0) :
    (poly.comp (CPolynomial.C factor * CPolynomial.X)).comp
      (CPolynomial.C factor⁻¹ * CPolynomial.X) = poly := by
  apply CPolynomial.toPoly_injective
  simp only [CPolynomial.toPoly_comp, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly, Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp]
  rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hfactor, Polynomial.C_1, one_mul,
    Polynomial.comp_X]

/-- Interpolate on a shifted domain and undo the shift to recover the original polynomial. -/
theorem rowPolynomial_coset_evaluations (k : ℕ) (hk : k ≤ 32) (poly : CPoly)
    (factor : Fp) (hfactor : factor ≠ 0) (hdegree : poly.natDegree < 2 ^ k) :
    (rowPolynomial (omegaOf k)
      (fun index : Fin (2 ^ k) => poly.eval (factor * omegaOf k ^ index.val))).comp
        (CPolynomial.C factor⁻¹ * CPolynomial.X) = poly := by
  have hrotated := rowPolynomial_evaluations k hk
    (poly.comp (CPolynomial.C factor * CPolynomial.X))
    (by simpa only [CPolynomial.natDegree_comp_C_mul_X poly hfactor] using hdegree)
  simp only [CPolynomial.eval_comp_C_mul_X] at hrotated
  rw [hrotated, polynomial_comp_inverse_rotation poly factor hfactor]

/-- The fixed numerator interpolation points use a size-32768 coset. -/
def plonkNumeratorNode (index : Fin (2 ^ 15)) : Fp := omegaOf 16 * omegaOf 15 ^ index.val

/-- The fixed coset multiplier is invertible. -/
theorem plonkNumeratorShift_ne_zero : omegaOf 16 ≠ 0 :=
  (omegaOf_primitiveRoot 16 (by decide)).ne_zero (by decide)

/-- Every interpolation point lies outside the original 2048-row domain. -/
theorem plonkNumeratorNode_off_domain (index : Fin (2 ^ 15)) :
    plonkNumeratorNode index ^ 2048 ≠ 1 := by
  have hsmall := (omegaOf_primitiveRoot 15 (by decide)).pow_eq_one
  have hshift := (omegaOf_primitiveRoot 16 (by decide)).pow_ne_one_of_pos_of_lt
    (by decide : (2 ^ 15 : ℕ) ≠ 0) (by decide : (2 ^ 15 : ℕ) < 2 ^ 16)
  have hnode : plonkNumeratorNode index ^ (2 ^ 15) = omegaOf 16 ^ (2 ^ 15) := by
    rw [plonkNumeratorNode, mul_pow, ← pow_mul, Nat.mul_comm index.val,
      pow_mul, hsmall, one_pow, mul_one]
  intro h
  apply hshift
  rw [← hnode]
  rw [show (2 ^ 15 : ℕ) = 2048 * 16 from by decide, pow_mul, h, one_pow]

end Zcash.Snark.ZeroKnowledge
