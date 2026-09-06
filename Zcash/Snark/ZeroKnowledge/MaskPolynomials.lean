import Zcash.Snark.ZeroKnowledge.SparseIpa
import Zcash.Snark.ZeroKnowledge.LinearMask
import Zcash.Snark.Soundness.Multiopen.Decode

/-!
# Connecting mask vectors to the existing polynomial representation

The sparse IPA fold uses coefficient vectors. This module proves that its vector is exactly
the polynomial from Common #225 under the existing `coeffsToPoly` conversion, and that the
linear mask from Common #267 gives the modeled pair of evaluations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open CompPoly

private theorem coeffsToPoly_add {n : ℕ} (a b : Fin n → Fp) :
    coeffsToPoly (a + b) = coeffsToPoly a + coeffsToPoly b := by
  apply CPolynomial.toPoly_injective
  simp [coeffsToPoly, CPolynomial.toPoly_sum, CPolynomial.toPoly_pow,
    add_mul, Finset.sum_add_distrib]

private theorem coeffsToPoly_sub {n : ℕ} (a b : Fin n → Fp) :
    coeffsToPoly (a - b) = coeffsToPoly a - coeffsToPoly b := by
  apply CPolynomial.toPoly_injective
  simp [coeffsToPoly, CPolynomial.toPoly_sum, CPolynomial.toPoly_pow,
    Polynomial.C_sub, sub_mul, Finset.sum_sub_distrib]

private theorem coeffsToPoly_smul {n : ℕ} (r : Fp) (a : Fin n → Fp) :
    coeffsToPoly (r • a) = CPolynomial.C r * coeffsToPoly a := by
  apply CPolynomial.toPoly_injective
  simp [coeffsToPoly, CPolynomial.toPoly_sum, CPolynomial.toPoly_pow,
    Polynomial.C_mul, mul_assoc, Finset.mul_sum]

private theorem coeffsToPoly_sum {I : Type*} {n : ℕ} (s : Finset I)
    (a : I → Fin n → Fp) : coeffsToPoly (∑ i ∈ s, a i) = ∑ i ∈ s, coeffsToPoly (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply CPolynomial.toPoly_injective
    simp [coeffsToPoly]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coeffsToPoly_add, ih]

private theorem coeffsToPoly_single {n : ℕ} (i : Fin n) (v : Fp) :
    coeffsToPoly (Pi.single i v) = CPolynomial.C v * CPolynomial.X ^ i.val := by
  unfold coeffsToPoly
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    apply CPolynomial.toPoly_injective
    simp
  · simp

/-- The folded sparse coefficient vector is exactly the stated Common #225 polynomial. -/
theorem coeffsToPoly_sparseIpaCoefficients {k : ℕ} (q : Fp) (alphas : Fin k → Fp) :
    coeffsToPoly (sparseIpaCoefficients q alphas) = sparseIpaPolynomial q alphas := by
  rw [sparseIpaCoefficients, coeffsToPoly_sum]
  simp only [coeffsToPoly_smul, coeffsToPoly_sub, coeffsToPoly_single]
  apply CPolynomial.toPoly_injective
  simp [sparseIpaPolynomial, CPolynomial.toPoly_sum, CPolynomial.toPoly_pow, powerIndex]

/-- The coefficient polynomial used by Common #267. -/
def linearMaskPolynomial (coefficients : Fp × Fp) : CPoly :=
  CPolynomial.C coefficients.1 + CPolynomial.C coefficients.2 * CPolynomial.X

/-- The pair-distribution model uses precisely the two evaluations of this polynomial. -/
theorem linearMaskPolynomial_evaluations (coefficients : Fp × Fp) (x q : Fp) :
    ((linearMaskPolynomial coefficients).eval x, (linearMaskPolynomial coefficients).eval q) =
      linearMaskPair x q coefficients := by
  simp [linearMaskPolynomial, linearMaskPair]

end Zcash.Snark.ZeroKnowledge
