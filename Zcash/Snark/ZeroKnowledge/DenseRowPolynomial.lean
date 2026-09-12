import Zcash.Snark.ZeroKnowledge.DensePolynomial
import Zcash.Snark.ZeroKnowledge.RowPolynomialCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp omegaOf omegaOf_powers_injective)
open Zcash.Snark CompPoly

/-- The stored finite-vector decoder is the source's coefficient-to-polynomial map. -/
theorem densePolynomial_ofFn {n : ℕ} (values : Fin n → Fp) :
    densePolynomial (List.ofFn values) = coeffsToPoly values := by
  induction n with
  | zero => simp [densePolynomial, coeffsToPoly]
  | succ n ih =>
    rw [List.ofFn_succ, densePolynomial, ih]
    simp only [coeffsToPoly, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    ring

/-- A materialized complete coefficient vector represents the original canonical polynomial. -/
theorem densePolynomial_coefficients {n : ℕ} (poly : CPoly) (hdegree : poly.natDegree < n) :
    densePolynomial (List.ofFn (polynomialCoefficients n poly)) = poly := by
  rw [densePolynomial_ofFn, coeffsToPoly_polynomialCoefficients poly hdegree]

/-- The counted inverse DFT supplies the actual row polynomial in stored-coefficient form. -/
theorem densePolynomial_rowCoefficientsCosted (costs : FieldOperationCosts) (k : ℕ) (hk : k ≤ 32)
    (omegaAccess : ℕ) (values : Fin (2 ^ k) → Fp × ℕ) :
    densePolynomial (rowCoefficientsCosted costs (omegaOf k, omegaAccess) values).1 =
      rowPolynomial (omegaOf k) (fun row => (values row).1) := by
  rw [rowCoefficientsCosted_result costs k hk omegaAccess values]
  exact densePolynomial_coefficients _
    (rowPolynomial_natDegree_lt (omegaOf_powers_injective k hk) (Nat.two_pow_pos k))

end Zcash.Snark.ZeroKnowledge
