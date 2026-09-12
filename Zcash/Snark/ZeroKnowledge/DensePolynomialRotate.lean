import Zcash.Snark.ZeroKnowledge.DensePolynomial

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Scale successive coefficients by a running power, with every multiplication retained. -/
def denseRotateFromCosted (read multiply : ℕ) (factor : Fp) : Fp → List Fp → List Fp × ℕ
  | _, [] => ([], 1)
  | power, first :: rest =>
    let tail := denseRotateFromCosted read multiply factor (power * factor) rest
    ((first * power) :: tail.1, tail.2 + 3 * read + 2 * multiply + 4)

/-- The running-power invariant identifies the entire original polynomial composition. -/
theorem denseRotateFromCosted_result (read multiply : ℕ) (factor power : Fp) (values : List Fp) :
    densePolynomial (denseRotateFromCosted read multiply factor power values).1 =
      CPolynomial.C power * (densePolynomial values).comp (CPolynomial.C factor * CPolynomial.X) := by
  induction values generalizing power with
  | nil =>
    apply CPolynomial.toPoly_injective
    simp only [denseRotateFromCosted, densePolynomial, CPolynomial.toPoly_mul, CPolynomial.toPoly_zero,
      CPolynomial.toPoly_comp, Polynomial.zero_comp, mul_zero]
  | cons first rest ih =>
    simp only [denseRotateFromCosted, densePolynomial, ih]
    apply CPolynomial.toPoly_injective
    simp only [CPolynomial.toPoly_add, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
      CPolynomial.X_toPoly, CPolynomial.toPoly_comp, Polynomial.add_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.X_comp, Polynomial.C_mul]
    ring

/-- Rotation preserves all stored positions, including zero padding. -/
theorem denseRotateFromCosted_length (read multiply : ℕ) (factor power : Fp) (values : List Fp) :
    (denseRotateFromCosted read multiply factor power values).1.length = values.length := by
  induction values generalizing power <;> simp_all only [denseRotateFromCosted, List.length_nil, List.length_cons]

/-- Exact running-power cost is linear in the stored coefficient count. -/
theorem denseRotateFromCosted_cost (read multiply : ℕ) (factor power : Fp) (values : List Fp) :
    (denseRotateFromCosted read multiply factor power values).2 =
      values.length * (3 * read + 2 * multiply + 4) + 1 := by
  induction values generalizing power with
  | nil => simp [denseRotateFromCosted]
  | cons first rest ih => simp only [denseRotateFromCosted, ih, List.length_cons]; ring

/-- Rotate a stored polynomial, retaining preparation of the rotation factor even on empty input. -/
def denseRotateCosted (read multiply : ℕ) (factor : Fp × ℕ) (values : List Fp) : List Fp × ℕ :=
  let result := denseRotateFromCosted read multiply factor.1 1 values
  (result.1, factor.2 + result.2 + 1)

/-- Cost erasure is exactly composition by the original linear variable rotation. -/
theorem denseRotateCosted_result (read multiply : ℕ) (factor : Fp × ℕ) (values : List Fp) :
    densePolynomial (denseRotateCosted read multiply factor values).1 =
      (densePolynomial values).comp (CPolynomial.C factor.1 * CPolynomial.X) := by
  rw [denseRotateCosted, denseRotateFromCosted_result]
  apply CPolynomial.toPoly_injective
  simp only [CPolynomial.toPoly_mul, CPolynomial.C_toPoly, Polynomial.C_1, one_mul]

/-- The complete rotation leaves the materialized coefficient size unchanged. -/
theorem denseRotateCosted_length (read multiply : ℕ) (factor : Fp × ℕ) (values : List Fp) :
    (denseRotateCosted read multiply factor values).1.length = values.length :=
  denseRotateFromCosted_length _ _ _ _ _

/-- The complete bound includes factor preparation and the entire coefficient pass. -/
theorem denseRotateCosted_cost (read multiply : ℕ) (factor : Fp × ℕ) (values : List Fp) :
    (denseRotateCosted read multiply factor values).2 =
      factor.2 + values.length * (3 * read + 2 * multiply + 4) + 2 := by
  simp only [denseRotateCosted, denseRotateFromCosted_cost]
  omega

end Zcash.Snark.ZeroKnowledge
