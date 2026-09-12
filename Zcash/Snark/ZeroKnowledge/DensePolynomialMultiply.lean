import Zcash.Snark.ZeroKnowledge.DensePolynomialScale

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Multiply stored polynomials by coefficient scaling, shifting, and counted list addition. -/
def denseMulCosted (read add multiply : ℕ) : List Fp → List Fp → List Fp × ℕ
  | [], _ => ([], 1)
  | first :: rest, right =>
    let upper := denseMulCosted read add multiply rest right
    let term := denseScaleCosted read multiply (first, read + 1) right
    let result := denseAddCosted read add term.1 (0 :: upper.1)
    (result.1, upper.2 + term.2 + result.2 + 2)

/-- The stored algorithm implements the existing polynomial multiplication exactly. -/
theorem denseMulCosted_result (read add multiply : ℕ) (left right : List Fp) :
    densePolynomial (denseMulCosted read add multiply left right).1 =
      densePolynomial left * densePolynomial right := by
  induction left with
  | nil => simp [denseMulCosted, densePolynomial]
  | cons first rest ih =>
    simp only [denseMulCosted, denseAddCosted_result, denseScaleCosted_result, densePolynomial,
      CPolynomial.C_zero, zero_add, ih]
    ring

/-- Every intermediate coefficient list fits the sum of the two input widths. -/
theorem denseMulCosted_length_le (read add multiply : ℕ) (left right : List Fp) :
    (denseMulCosted read add multiply left right).1.length ≤ left.length + right.length := by
  induction left with
  | nil => simp [denseMulCosted]
  | cons first rest ih =>
    simp only [denseMulCosted, denseAddCosted_length, denseScaleCosted_length, List.length_cons]
    omega

/-- Complete multiplication cost is quadratic in the input widths with explicit field prices. -/
theorem denseMulCosted_cost_le (read add multiply : ℕ) (left right : List Fp) :
    (denseMulCosted read add multiply left right).2 ≤
      left.length * (right.length * (3 * read + add + multiply + 5) + read + 6) + 1 := by
  induction left with
  | nil => simp [denseMulCosted]
  | cons first rest ih =>
    let upper := denseMulCosted read add multiply rest right
    let term := denseScaleCosted read multiply (first, read + 1) right
    have ht := denseScaleCosted_cost_le read multiply (first, read + 1) right
    have hn : term.1.length = right.length := denseScaleCosted_length _ _ _ _
    have ha := denseAddCosted_cost_le read add term.1 (0 :: upper.1)
    rw [hn] at ha
    change upper.2 + term.2 + (denseAddCosted read add term.1 (0 :: upper.1)).2 + 2 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    nlinarith

/-- Subtract stored polynomials while retaining every negation and addition operation. -/
def denseSubCosted (read add negate : ℕ) (left right : List Fp) : List Fp × ℕ :=
  let negative := denseNegCosted read negate right
  let result := denseAddCosted read add left negative.1
  (result.1, negative.2 + result.2 + 1)

/-- Stored subtraction has exactly the original polynomial meaning. -/
theorem denseSubCosted_result (read add negate : ℕ) (left right : List Fp) :
    densePolynomial (denseSubCosted read add negate left right).1 =
      densePolynomial left - densePolynomial right := by
  simp only [denseSubCosted, denseAddCosted_result, denseNegCosted_result, sub_eq_add_neg]

/-- Subtraction preserves the maximum input width. -/
theorem denseSubCosted_length (read add negate : ℕ) (left right : List Fp) :
    (denseSubCosted read add negate left right).1.length = max left.length right.length := by
  simp only [denseSubCosted, denseAddCosted_length, denseNegCosted_length]

/-- Complete subtraction cost retains both inputs and every field operation. -/
theorem denseSubCosted_cost_le (read add negate : ℕ) (left right : List Fp) :
    (denseSubCosted read add negate left right).2 ≤
      right.length * (read + negate + 2) + left.length * (2 * read + add + 2) + 3 := by
  have hn := denseNegCosted_cost_le read negate right
  have ha := denseAddCosted_cost_le read add left (denseNegCosted read negate right).1
  dsimp only [denseSubCosted]
  omega

end Zcash.Snark.ZeroKnowledge
