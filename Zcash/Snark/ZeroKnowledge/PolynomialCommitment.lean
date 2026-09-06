import Zcash.Snark.ZeroKnowledge.PlonkOpening

/-!
# Polynomial commitments and the prover's blind folds

The prover folds each polynomial and its commitment blind with identical Horner weights.
These identities relate that computation to a fold of the public commitment points. The
coefficient conversion is exact once the polynomial's degree is below the IPA vector size.
No discrete-log or binding assumption is needed for these correctness identities.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open CompPoly

/-- The first `n` coefficients, in the order supplied to the IPA and coefficient commitment. -/
def polynomialCoefficients (n : ℕ) (poly : CPoly) : Fin n → Fp :=
  fun i => poly.coeff i.val

/-- Bounded-degree polynomials are recovered exactly from this finite coefficient vector. -/
theorem coeffsToPoly_polynomialCoefficients {n : ℕ} (poly : CPoly) (hdegree : poly.natDegree < n) :
    coeffsToPoly (polynomialCoefficients n poly) = poly := by
  apply CPolynomial.toPoly_injective
  simp only [coeffsToPoly, polynomialCoefficients, CPolynomial.toPoly_sum, CPolynomial.toPoly_mul,
    CPolynomial.C_toPoly, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (poly.coeff i) * Polynomial.X ^ i)]
  simpa only [CPolynomial.coeff_toPoly] using
    (Polynomial.as_sum_range_C_mul_X_pow' poly.toPoly
      (by simpa only [CPolynomial.natDegree_toPoly] using hdegree)).symm

/-- The IPA vector evaluates to the actual polynomial value, rather than a truncated value. -/
theorem coefficientEvaluation_polynomialCoefficients {k : ℕ} (poly : CPoly) (q : Fp)
    (hdegree : poly.natDegree < 2 ^ k) :
    coefficientEvaluation k q (polynomialCoefficients (2 ^ k) poly) = poly.eval q := by
  calc
    _ = (coeffsToPoly (polynomialCoefficients (2 ^ k) poly)).eval q := by
      simp [coeffsToPoly, coefficientEvaluation, CPolynomial.eval_finsetSum]
    _ = _ := congrArg (fun p : CPoly => p.eval q) (coeffsToPoly_polynomialCoefficients poly hdegree)

/-- A polynomial Horner step induces exactly the same linear step on its coefficient vector. -/
theorem polynomialCoefficients_horner {n : ℕ} (acc poly : CPoly) (challenge : Fp) :
    polynomialCoefficients n (acc * CPolynomial.C challenge + poly) =
      challenge • polynomialCoefficients n acc + polynomialCoefficients n poly := by
  funext i
  simp only [polynomialCoefficients, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [CPolynomial.coeff_toPoly, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.C_toPoly, Polynomial.coeff_add, Polynomial.coeff_mul_C]
  simp only [CPolynomial.coeff_toPoly, mul_comm]

/-- Horner folds preserve a common strict polynomial-degree bound. -/
theorem plonkPolynomialFold_natDegree_lt {n : ℕ} (hn : 0 < n) (challenge : Fp) (polys : List CPoly)
    (hdegree : ∀ poly ∈ polys, poly.natDegree < n) :
    (plonkPolynomialFold challenge polys).natDegree < n := by
  have hstep (acc poly : CPoly) (ha : acc.natDegree < n) (hp : poly.natDegree < n) :
      (acc * CPolynomial.C challenge + poly).natDegree < n := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_add, CPolynomial.toPoly_mul, CPolynomial.C_toPoly]
    apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (Polynomial.natDegree_mul_C_le _ _) (by simpa only [CPolynomial.natDegree_toPoly] using ha)
    · simpa only [CPolynomial.natDegree_toPoly] using hp
  have h (acc : CPoly) (ha : acc.natDegree < n) :
      (polys.foldl (fun acc poly => acc * CPolynomial.C challenge + poly) acc).natDegree < n := by
    induction polys generalizing acc with
    | nil => exact ha
    | cons poly polys ih =>
      apply ih (fun p hp => hdegree p (List.mem_cons_of_mem _ hp))
      exact hstep acc poly ha (hdegree poly List.mem_cons_self)
  exact h 0 (by simpa using hn)

section Commitments

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The pinned coefficient commitment, including its own scalar blind. -/
def polynomialCommitment {n : ℕ} (generators : Fin n → G) (W : G) (poly : CPoly) (blind : Fp) : G :=
  commitGen generators (polynomialCoefficients n poly) + blind • W

/-- Zero polynomial and zero blind give the identity commitment. -/
theorem polynomialCommitment_zero {n : ℕ} (generators : Fin n → G) (W : G) :
    polynomialCommitment generators W 0 0 = 0 := by
  simp only [polynomialCommitment, polynomialCoefficients, commitGen, CPolynomial.coeff_zero,
    zero_smul, Finset.sum_const_zero, add_zero]

/-- Updating both the polynomial and its blind agrees with the public commitment update. -/
theorem polynomialCommitment_horner {n : ℕ} (generators : Fin n → G) (W : G)
    (acc poly : CPoly) (accBlind blind challenge : Fp) :
    polynomialCommitment generators W (acc * CPolynomial.C challenge + poly)
        (accBlind * challenge + blind) =
      challenge • polynomialCommitment generators W acc accBlind +
        polynomialCommitment generators W poly blind := by
  simp only [polynomialCommitment, polynomialCoefficients_horner, commitGen_add_left,
    commitGen_smul_left, add_smul, smul_add, smul_smul]
  rw [mul_comm accBlind challenge]
  abel

/-- Collapsing quotient pieces folds their blinds with exactly the same scalar weights. -/
theorem polynomialCommitment_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (generators : Fin n → G) (W : G) (weights : ι → Fp)
    (polys : ι → CPoly) (blinds : ι → Fp) :
    polynomialCommitment generators W (∑ i, CPolynomial.C (weights i) * polys i)
        (∑ i, weights i * blinds i) =
      ∑ i, weights i • polynomialCommitment generators W (polys i) (blinds i) := by
  classical
  simp only [polynomialCommitment, commitGen, polynomialCoefficients,
    CPolynomial.coeff_finset_sum, CPolynomial.coeff_C_mul, Finset.sum_smul,
    mul_smul, smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

/-- Public commitment points are combined by the same Horner convention. -/
def commitmentHornerFold (challenge : Fp) (points : List G) : G :=
  points.foldl (fun acc point => challenge • acc + point) 0

/-- Every blind, including a public polynomial's constant blind, participates in the same fold. -/
theorem polynomialCommitment_fold {n : ℕ} (generators : Fin n → G) (W : G)
    (challenge : Fp) (polys : List (CPoly × Fp)) :
    polynomialCommitment generators W (plonkPolynomialFold challenge (polys.map Prod.fst))
        (plonkScalarFold challenge (polys.map Prod.snd)) =
      commitmentHornerFold challenge (polys.map fun pair => polynomialCommitment generators W pair.1 pair.2) := by
  have h (acc : CPoly) (blind : Fp) :
      polynomialCommitment generators W
          (polys.foldl (fun p pair => p * CPolynomial.C challenge + pair.1) acc)
          (polys.foldl (fun r pair => r * challenge + pair.2) blind) =
        polys.foldl (fun point pair => challenge • point + polynomialCommitment generators W pair.1 pair.2)
          (polynomialCommitment generators W acc blind) := by
    induction polys generalizing acc blind with
    | nil => rfl
    | cons pair polys ih =>
      simp only [List.foldl_cons]
      rw [ih, polynomialCommitment_horner]
  simpa only [plonkPolynomialFold, plonkScalarFold, commitmentHornerFold, List.foldl_map,
    polynomialCommitment_zero] using h 0 0

end Commitments

end Zcash.Snark.ZeroKnowledge
