import Zcash.Snark.ZeroKnowledge.DensePolynomial
import Zcash.Snark.Soundness.Multiopen.NodeBinding

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Synthetic division scans stored coefficients once, keeping its quotient and remainder. -/
def denseSyntheticCosted (read add multiply : ℕ) (root : Fp) : List Fp → (List Fp × Fp) × ℕ
  | [] => (([], 0), 1)
  | first :: rest =>
    let upper := denseSyntheticCosted read add multiply root rest
    ((upper.1.2 :: upper.1.1, first + root * upper.1.2), upper.2 + read + add + multiply + 5)

/-- The returned quotient and constant remainder satisfy the full polynomial identity on every input. -/
theorem denseSyntheticCosted_identity (read add multiply : ℕ) (root : Fp) (values : List Fp) :
    densePolynomial values = CPolynomial.C (denseSyntheticCosted read add multiply root values).1.2 +
      (CPolynomial.X - CPolynomial.C root) *
        densePolynomial (denseSyntheticCosted read add multiply root values).1.1 := by
  induction values with
  | nil => simp [denseSyntheticCosted, densePolynomial]
  | cons first rest ih =>
    simp only [denseSyntheticCosted, densePolynomial, CPolynomial.C_add, CPolynomial.C_mul, ih]
    ring

/-- Padding is preserved, so repeated divisions never enlarge the materialized coefficient array. -/
theorem denseSyntheticCosted_length (read add multiply : ℕ) (root : Fp) (values : List Fp) :
    (denseSyntheticCosted read add multiply root values).1.1.length = values.length := by
  induction values <;> simp_all only [denseSyntheticCosted, List.length_cons, List.length_nil]

/-- Exact cost of the complete synthetic-division loop. -/
theorem denseSyntheticCosted_cost (read add multiply : ℕ) (root : Fp) (values : List Fp) :
    (denseSyntheticCosted read add multiply root values).2 = values.length * (read + add + multiply + 5) + 1 := by
  induction values with
  | nil => simp [denseSyntheticCosted]
  | cons first rest ih =>
    simp only [denseSyntheticCosted, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Compute a linear quotient while retaining preparation of its root on all inputs. -/
def denseDivLinearCosted (read add multiply : ℕ) (root : Fp × ℕ) (values : List Fp) : List Fp × ℕ :=
  let result := denseSyntheticCosted read add multiply root.1 values
  (result.1.1, root.2 + result.2 + 1)

/-- The returned list represents the existing executable polynomial quotient, without an exact-divisibility premise. -/
theorem denseDivLinearCosted_result (read add multiply : ℕ) (root : Fp × ℕ) (values : List Fp) :
    densePolynomial (denseDivLinearCosted read add multiply root values).1 =
      (densePolynomial values).div (CPolynomial.X - CPolynomial.C root.1) := by
  let result := denseSyntheticCosted read add multiply root.1 values
  have hi := congrArg CPolynomial.toPoly (denseSyntheticCosted_identity read add multiply root.1 values)
  simp only [CPolynomial.toPoly_add, CPolynomial.C_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_sub, CPolynomial.X_toPoly] at hi
  have hu := Polynomial.div_modByMonic_unique (densePolynomial result.1.1).toPoly
    (Polynomial.C result.1.2) (Polynomial.monic_X_sub_C root.1)
    ⟨hi.symm, by simpa only [Polynomial.degree_X_sub_C] using
      (Polynomial.degree_C_lt (a := result.1.2))⟩
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.div_toPoly_eq_div, CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly,
    ← Polynomial.divByMonic_eq_div _ (Polynomial.monic_X_sub_C root.1)]
  exact hu.1.symm

/-- Linear division keeps the same bounded coefficient storage. -/
theorem denseDivLinearCosted_length (read add multiply : ℕ) (root : Fp × ℕ) (values : List Fp) :
    (denseDivLinearCosted read add multiply root values).1.length = values.length :=
  denseSyntheticCosted_length _ _ _ _ _

/-- Complete linear-division cost includes the root and all coefficients. -/
theorem denseDivLinearCosted_cost (read add multiply : ℕ) (root : Fp × ℕ) (values : List Fp) :
    (denseDivLinearCosted read add multiply root values).2 =
      root.2 + values.length * (read + add + multiply + 5) + 2 := by
  rw [denseDivLinearCosted, denseSyntheticCosted_cost]
  omega

end Zcash.Snark.ZeroKnowledge
