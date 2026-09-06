import Zcash.Snark.ZeroKnowledge.PolynomialCommitment
import Zcash.Snark.Soundness.Multiopen.NodeBinding
import Mathlib.Data.Fintype.BigOperators

/-!
# Computed quotient pieces

The prover cuts the quotient coefficient vector into eight consecutive blocks of
2048 coefficients. These definitions perform that cut directly. Recombination and
degree bounds are proved for arbitrary block sizes before specializing to the pinned
PLONK quotient. No quotient pieces are supplied by a caller.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open CompPoly

/-- A consecutive block of `size` coefficients, beginning at `size * block`. -/
def polynomialCoefficientBlock (size block : ℕ) (poly : CPoly) : CPoly :=
  coeffsToPoly (fun i : Fin size => poly.coeff (size * block + i.val))

/-- Every nonempty coefficient block has degree strictly below its size. -/
theorem polynomialCoefficientBlock_natDegree_lt {size : ℕ} (hsize : 0 < size)
    (block : ℕ) (poly : CPoly) : (polynomialCoefficientBlock size block poly).natDegree < size :=
  coeffsToPoly_natDegree_lt hsize _

/-- Consecutive blocks reassemble exactly every polynomial fitting in their combined capacity. -/
theorem polynomialCoefficientBlocks_recombine {size count : ℕ} (poly : CPoly)
    (hdegree : poly.natDegree < count * size) :
    (∑ j : Fin count, CPolynomial.X ^ (size * j.val) * polynomialCoefficientBlock size j.val poly) = poly := by
  calc
    _ = ∑ j : Fin count, ∑ i : Fin size,
        CPolynomial.C (poly.coeff (size * j.val + i.val)) * CPolynomial.X ^ (size * j.val + i.val) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [polynomialCoefficientBlock, coeffsToPoly, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
      ring
    _ = ∑ ji : Fin count × Fin size,
        CPolynomial.C (poly.coeff (size * ji.1.val + ji.2.val)) *
          CPolynomial.X ^ (size * ji.1.val + ji.2.val) := by
      rw [Fintype.sum_prod_type]
    _ = coeffsToPoly (polynomialCoefficients (count * size) poly) := by
      simp only [coeffsToPoly, polynomialCoefficients]
      apply Fintype.sum_equiv (finProdFinEquiv : Fin count × Fin size ≃ Fin (count * size))
      intro ji
      simp only [finProdFinEquiv, Equiv.coe_fn_mk]
      rw [Nat.add_comm]
    _ = poly := coeffsToPoly_polynomialCoefficients poly hdegree

/-- At `x`, replacing the powers of `X` by powers of `x` preserves the recombined evaluation. -/
theorem polynomialCoefficientBlocks_eval {size count : ℕ} (poly : CPoly) (x : Fp)
    (hdegree : poly.natDegree < count * size) :
    (∑ j : Fin count, CPolynomial.C (x ^ (size * j.val)) *
      polynomialCoefficientBlock size j.val poly).eval x = poly.eval x := by
  calc
    _ = (∑ j : Fin count, CPolynomial.X ^ (size * j.val) *
        polynomialCoefficientBlock size j.val poly).eval x := by
      simp only [CPolynomial.eval_finsetSum, CPolynomial.eval_mul, CPolynomial.eval_C,
        CPolynomial.eval_pow, CPolynomial.eval_X]
    _ = poly.eval x := congrArg (fun p : CPoly => p.eval x)
      (polynomialCoefficientBlocks_recombine poly hdegree)

/-- Division by a size-`n` row-domain polynomial, using the executable polynomial algorithm. -/
def domainQuotient (n : ℕ) (numerator : CPoly) : CPoly :=
  numerator.div (CPolynomial.X ^ n - 1)

/-- The honest quotient at the pinned row-domain size. -/
def plonkQuotient (numerator : CPoly) : CPoly :=
  domainQuotient 2048 numerator

/-- All eight honest quotient pieces, cut directly from the computed quotient. -/
def plonkQuotientPieces (numerator : CPoly) : Fin 8 → CPoly :=
  fun j => polynomialCoefficientBlock 2048 j.val (plonkQuotient numerator)

/-- The computed pieces always satisfy their commitment and IPA degree bound. -/
theorem plonkQuotientPieces_natDegree_lt (numerator : CPoly) (j : Fin 8) :
    (plonkQuotientPieces numerator j).natDegree < 2048 :=
  polynomialCoefficientBlock_natDegree_lt (size := 2048) (by decide) j.val (plonkQuotient numerator)

/-- Exact degree of domain division, including zero and short numerators. -/
theorem domainQuotient_natDegree {n : ℕ} (hn : n ≠ 0) (numerator : CPoly) :
    (domainQuotient n numerator).natDegree = numerator.natDegree - n := by
  rw [CPolynomial.natDegree_toPoly, domainQuotient, CPolynomial.div_toPoly_eq_div,
    CPolynomial.toPoly_sub, CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.toPoly_one]
  have hmonic0 := Polynomial.monic_X_pow_sub_C (1 : Fp) hn
  have hmonic : (Polynomial.X ^ n - (1 : Polynomial Fp)).Monic := by
    simpa only [Polynomial.C_1] using hmonic0
  rw [← Polynomial.divByMonic_eq_div _ hmonic, Polynomial.natDegree_divByMonic _ hmonic]
  rw [← Polynomial.C_1 (R := Fp), Polynomial.natDegree_X_pow_sub_C]
  rw [← CPolynomial.natDegree_toPoly]

/-- The exact degree drop at the pinned domain size. -/
theorem plonkQuotient_natDegree (numerator : CPoly) :
    (plonkQuotient numerator).natDegree = numerator.natDegree - 2048 :=
  domainQuotient_natDegree (n := 2048) (by decide) numerator

/-- Nine domain blocks suffice for the numerator, hence eight for the computed quotient. -/
theorem plonkQuotient_natDegree_lt (numerator : CPoly) (hdegree : numerator.natDegree < 9 * 2048) :
    (plonkQuotient numerator).natDegree < 8 * 2048 := by
  rw [plonkQuotient_natDegree]
  omega

/-- Exact divisibility makes the computed domain quotient satisfy its polynomial identity. -/
theorem domainQuotient_identity {n : ℕ} (hn : n ≠ 0) (numerator : CPoly)
    (hdiv : (CPolynomial.X ^ n - 1 : CPoly) ∣ numerator) :
    domainQuotient n numerator * (CPolynomial.X ^ n - 1) = numerator := by
  obtain ⟨quotient, hquotient⟩ := hdiv
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.toPoly_mul, domainQuotient, CPolynomial.div_toPoly_eq_div]
  have hdivisor : (CPolynomial.X ^ n - (1 : CPoly)).toPoly ≠ 0 := by
    simp only [CPolynomial.toPoly_sub, CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.toPoly_one]
    have hmonic := Polynomial.monic_X_pow_sub_C (1 : Fp) hn
    simpa only [Polynomial.C_1] using hmonic.ne_zero
  rw [hquotient, CPolynomial.toPoly_mul, mul_div_cancel_left₀ _ hdivisor]
  exact mul_comm _ _

/-- Exact divisibility gives the pinned quotient identity. -/
theorem plonkQuotient_identity (numerator : CPoly)
    (hdiv : (CPolynomial.X ^ 2048 - 1 : CPoly) ∣ numerator) :
    plonkQuotient numerator * (CPolynomial.X ^ 2048 - 1) = numerator :=
  domainQuotient_identity (n := 2048) (by decide) numerator hdiv

/-- Outside the row domain, the honest collapsed pieces give the numerator divided by `x^n - 1`. -/
theorem plonkQuotientPieces_eval (numerator : CPoly) (x : Fp)
    (hdegree : numerator.natDegree < 9 * 2048)
    (hdiv : (CPolynomial.X ^ 2048 - 1 : CPoly) ∣ numerator) (hx : x ^ 2048 ≠ 1) :
    (plonkCollapsedQuotient x (plonkQuotientPieces numerator)).eval x =
      numerator.eval x / (x ^ 2048 - 1) := by
  have hpieces := polynomialCoefficientBlocks_eval (size := 2048) (count := 8)
    (plonkQuotient numerator) x (plonkQuotient_natDegree_lt numerator hdegree)
  change (plonkCollapsedQuotient x (plonkQuotientPieces numerator)).eval x =
    (plonkQuotient numerator).eval x at hpieces
  rw [hpieces]
  have h := congrArg (fun poly : CPoly => poly.eval x) (plonkQuotient_identity numerator hdiv)
  simp only [CPolynomial.eval_mul, CPolynomial.eval_sub, CPolynomial.eval_pow,
    CPolynomial.eval_X, CPolynomial.eval_one] at h
  exact (eq_div_iff (sub_ne_zero.mpr hx)).mpr h

end Zcash.Snark.ZeroKnowledge
