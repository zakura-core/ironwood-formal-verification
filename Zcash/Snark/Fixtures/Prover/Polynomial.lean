import CompPoly.Univariate.NTT.Interpolation
import CompPoly.Univariate.NTT.FastMul
import Zcash.Snark.ZeroKnowledge.DensePolynomial
import Zcash.Snark.ZeroKnowledge.DensePolynomialRotate
import Zcash.Snark.ZeroKnowledge.PlonkPublicRows

/-!
# Polynomial preparation for captured prover executions

The replay uses CompPoly's proved NTT for interpolation and multiplication.
The equalities below connect these computations to the same canonical row
polynomials used by the reference prover. No compiler overrides are installed.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark Zcash.Snark.ZeroKnowledge CompPoly CPolynomial CPolynomial.NTT

/-- Materialize a finite function as data, so later reads cannot reconstruct its cache. -/
@[noinline] def cacheFn {α : Type*} {n : ℕ} (f : Fin n → α) : Vector α n := Vector.ofFn f

/-- Caching changes storage and evaluation order but preserves every function value. -/
theorem cacheFn_result {α : Type*} {n : ℕ} (f : Fin n → α) : (cacheFn f).get = f := by
  funext i
  simp [cacheFn, Vector.get]

/-- Reading a canonical polynomial's stored coefficients preserves its polynomial value. -/
theorem storedCoefficients_result (poly : CPoly) : densePolynomial poly.val.toList = poly := by
  rw [densePolynomial_ofArray, Array.toArray_toList]
  apply CPolynomial.toPoly_injective
  exact CPolynomial.ofArray_toPoly poly.val

/-- A supported Pasta root gives the complete checked NTT domain. -/
def domain (k : ℕ) (hk : k ≤ 32) : Domain Fp where
  logN := k
  omega := omegaOf k
  primitive := omegaOf_primitiveRoot k hk
  natCast_ne_zero := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_ne_zero _ (by decide +kernel : (2 : Fp) ≠ 0)

/-- Interpolate every supplied row, retaining the full coefficient width. -/
def rowCoefficients (k : ℕ) (hk : k ≤ 32) (rows : Fin (2 ^ k) → Fp) : List Fp :=
  (Inverse.inverseImpl (domain k hk) (Array.ofFn rows)).toList

/-- NTT interpolation preserves the declared domain size, including trailing zeros. -/
theorem rowCoefficients_length (k : ℕ) (hk : k ≤ 32) (rows : Fin (2 ^ k) → Fp) :
    (rowCoefficients k hk rows).length = 2 ^ k := by
  simp [rowCoefficients, Inverse.inverseImpl_correct, domain]

/-- The executable inverse transform denotes the reference prover's canonical row polynomial. -/
theorem rowCoefficients_result (k : ℕ) (hk : k ≤ 32) (rows : Fin (2 ^ k) → Fp) :
    densePolynomial (rowCoefficients k hk rows) = rowPolynomial (omegaOf k) rows := by
  rw [densePolynomial_ofArray]
  apply CPolynomial.toPoly_injective
  rw [toPoly_rowPolynomial]
  change (CPolynomial.ofArray (Inverse.inverseImpl (domain k hk) (Array.ofFn rows))).toPoly = _
  have h : CPolynomial.ofArray (Inverse.inverseImpl (domain k hk) (Array.ofFn rows)) =
      CLagrange.interpolatePow (omegaOf k) (loadNaturalVector (domain k hk) (Array.ofFn rows)) := by
    apply Subtype.ext
    exact Inverse.inverseImpl_interpolatePow_eq (domain k hk) (Array.ofFn rows)
  rw [h]
  change (CLagrange.interpolatePow (omegaOf k) (loadNaturalVector (domain k hk) (Array.ofFn rows))).toPoly = _
  rw [CLagrange.interpolatePow, CLagrange.cinterpolate_eq_interpolate]
  congr 1
  funext i
  simp [loadNaturalVector, domain, Vector.get]

/-- Canonical array construction avoids rebuilding the interpolant one monomial at a time. -/
def interpolateRows (k : ℕ) (hk : k ≤ 32) (rows : Fin (2 ^ k) → Fp) : CPoly :=
  CPolynomial.ofArray (rowCoefficients k hk rows).toArray

/-- The cached polynomial is the same row interpolant used in the protocol model. -/
theorem interpolateRows_result (k : ℕ) (hk : k ≤ 32) (rows : Fin (2 ^ k) → Fp) :
    interpolateRows k hk rows = rowPolynomial (omegaOf k) rows := by
  rw [interpolateRows, ← densePolynomial_ofArray, rowCoefficients_result]

/-- Dense products use a fitting NTT domain. Constant and linear factors go on the left
of CompPoly's coefficient loop, so its repeated sums have linear total size. -/
def multiply (left right : CPoly) : CPoly :=
  if min left.val.size right.val.size ≤ 2 then
    if left.val.size ≤ right.val.size then left * right else right * left
  else FastMul.withFallback (bestDomainForLength? 32 domain (fun _ _ => rfl)) left right

/-- Both multiplication branches compute the original polynomial product for every input. -/
theorem multiply_result (left right : CPoly) : multiply left right = left * right := by
  unfold multiply
  split
  · split
    · rfl
    · exact _root_.mul_comm right left
  · exact FastMul.withFallback_eq_mul _ left right

/-- An explicit arithmetic dictionary lets the existing generic constraint evaluator use the NTT. -/
private abbrev ringWithMultiplication (mul : CPoly → CPoly → CPoly)
    (hmul : ∀ left right, mul left right = left * right) : CommRing CPoly :=
  { (inferInstance : CommRing CPoly) with
    mul := mul
    mul_assoc := by
      intro a b c
      change mul (mul a b) c = mul a (mul b c)
      simp only [hmul]
      exact _root_.mul_assoc a b c
    one_mul := by
      intro a
      change mul 1 a = a
      rw [hmul, _root_.one_mul]
    mul_one := by
      intro a
      change mul a 1 = a
      rw [hmul, _root_.mul_one]
    npow_succ := by
      intro n a
      change a ^ (n + 1) = mul (a ^ n) a
      rw [hmul, _root_.pow_succ]
    zero_mul := by
      intro a
      change mul 0 a = 0
      rw [hmul, MulZeroClass.zero_mul]
    mul_zero := by
      intro a
      change mul a 0 = 0
      rw [hmul, MulZeroClass.mul_zero]
    left_distrib := by
      intro a b c
      change mul a (b + c) = mul a b + mul a c
      simp only [hmul]
      exact _root_.mul_add a b c
    right_distrib := by
      intro a b c
      change mul (a + b) c = mul a c + mul b c
      simp only [hmul]
      exact _root_.add_mul a b c
    mul_comm := by
      intro a b
      change mul a b = mul b a
      simp only [hmul]
      exact _root_.mul_comm a b }


/-- Dictionary equality is proved from multiplication equality, without a compiler override. -/
private theorem ringWithMultiplication_eq (mul : CPoly → CPoly → CPoly)
    (hmul : ∀ left right, mul left right = left * right) :
    ringWithMultiplication mul hmul = (inferInstance : CommRing CPoly) := by
  have h : mul = fun left right => left * right := funext fun left => funext (hmul left)
  subst mul
  rfl

/-- The replay passes this dictionary explicitly to the verifier's generic constraint builder. -/
abbrev polynomialRing : CommRing CPoly := ringWithMultiplication multiply multiply_result

/-- The NTT dictionary has exactly the same operations as the reference polynomial ring. -/
theorem polynomialRing_result : polynomialRing = (inferInstance : CommRing CPoly) :=
  ringWithMultiplication_eq multiply multiply_result

end Zcash.Snark.Fixtures.Prover
