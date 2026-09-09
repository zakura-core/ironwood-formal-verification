import Zcash.Snark.ZeroKnowledge.PolynomialCommitment
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Semantic interpretation of stored coefficients; counted arithmetic operates directly on the lists. -/
def densePolynomial : List Fp → CPoly
  | [] => 0
  | first :: rest => CPolynomial.C first + CPolynomial.X * densePolynomial rest

/-- Stored coefficients, including trailing zeros, have exactly the expected polynomial meaning. -/
theorem densePolynomial_coeff (values : List Fp) (index : ℕ) :
    (densePolynomial values).coeff index = values.getD index 0 := by
  induction values generalizing index with
  | nil => rw [densePolynomial, CPolynomial.coeff_zero]; rfl
  | cons first rest ih =>
    rw [densePolynomial, CPolynomial.coeff_add]
    cases index with
    | zero =>
      rw [CPolynomial.coeff_C, CPolynomial.coeff_X_mul_zero]
      simp only [ite_true, add_zero, List.getD_cons_zero]
    | succ index =>
      rw [CPolynomial.coeff_C, CPolynomial.coeff_X_mul_succ, ih]
      simp only [Nat.succ_ne_zero, ite_false, zero_add, List.getD_cons_succ]

/-- The semantic decoder is the existing canonical polynomial made from the same coefficients. -/
theorem densePolynomial_ofArray (values : List Fp) :
    densePolynomial values = CPolynomial.ofArray values.toArray := by
  apply CPolynomial.eq_iff_coeff.mpr
  intro index
  rw [densePolynomial_coeff, CPolynomial.coeff_ofArray]
  by_cases h : index < values.length <;> simp [Array.getD, List.getD_eq_getElem?_getD, h]

/-- A stored list has no nonzero coefficient beyond its materialized length. -/
theorem densePolynomial_coeff_eq_zero (values : List Fp) {index : ℕ} (h : values.length ≤ index) :
    (densePolynomial values).coeff index = 0 := by
  rw [densePolynomial_coeff]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Counted addition reads matching coefficients and shares either unmodified suffix. -/
def denseAddCosted (read add : ℕ) : List Fp → List Fp → List Fp × ℕ
  | [], right => (right, 1)
  | left, [] => (left, 1)
  | a :: left, b :: right =>
    let rest := denseAddCosted read add left right
    ((a + b) :: rest.1, rest.2 + 2 * read + add + 2)

/-- The addition algorithm implements the existing polynomial addition exactly. -/
theorem denseAddCosted_result (read add : ℕ) (left right : List Fp) :
    densePolynomial (denseAddCosted read add left right).1 = densePolynomial left + densePolynomial right := by
  induction left generalizing right with
  | nil => simp [denseAddCosted, densePolynomial]
  | cons a left ih =>
    cases right with
    | nil => simp [denseAddCosted, densePolynomial]
    | cons b right =>
      simp only [denseAddCosted, densePolynomial, ih, CPolynomial.C_add]
      ring

/-- Addition preserves the larger stored length, including noncanonical zero padding. -/
theorem denseAddCosted_length (read add : ℕ) (left right : List Fp) :
    (denseAddCosted read add left right).1.length = max left.length right.length := by
  induction left generalizing right with
  | nil => simp [denseAddCosted]
  | cons first left ih =>
    cases right with
    | nil => simp [denseAddCosted]
    | cons second right => simp only [denseAddCosted, List.length_cons, ih]; omega

/-- Addition traverses at most its left input and counts all field work. -/
theorem denseAddCosted_cost_le (read add : ℕ) (left right : List Fp) :
    (denseAddCosted read add left right).2 ≤ left.length * (2 * read + add + 2) + 1 := by
  induction left generalizing right with
  | nil => simp [denseAddCosted]
  | cons first left ih =>
    cases right with
    | nil => simp [denseAddCosted]
    | cons second right =>
      have h := ih right
      simp only [denseAddCosted, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end Zcash.Snark.ZeroKnowledge
