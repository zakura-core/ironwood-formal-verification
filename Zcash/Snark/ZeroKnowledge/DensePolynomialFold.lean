import Zcash.Snark.ZeroKnowledge.DensePolynomialScale
import Zcash.Snark.ZeroKnowledge.PlonkOpening

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Fold stored polynomials in the source's Horner order, charging every coefficient operation. -/
def densePolynomialFoldFromCosted (read add multiply : ℕ) (challenge : Fp × ℕ) :
    List (List Fp) → List Fp → List Fp × ℕ
  | [], initial => (initial, 1)
  | first :: rest, initial =>
    let scaled := denseScaleCosted read multiply challenge initial
    let next := denseAddCosted read add scaled.1 first
    let result := densePolynomialFoldFromCosted read add multiply challenge rest next.1
    (result.1, scaled.2 + next.2 + result.2 + read + 3)

/-- Erasure is the original polynomial Horner fold from the same initial polynomial. -/
theorem densePolynomialFoldFromCosted_result (read add multiply : ℕ) (challenge : Fp × ℕ)
    (polys : List (List Fp)) (initial : List Fp) :
    densePolynomial (densePolynomialFoldFromCosted read add multiply challenge polys initial).1 =
      (polys.map densePolynomial).foldl
        (fun acc poly => acc * CPolynomial.C challenge.1 + poly) (densePolynomial initial) := by
  induction polys generalizing initial with
  | nil => rfl
  | cons first rest ih =>
    simp only [densePolynomialFoldFromCosted, ih, List.map_cons, List.foldl_cons,
      denseAddCosted_result, denseScaleCosted_result]
    rw [mul_comm (CPolynomial.C challenge.1)]

/-- The stored width never exceeds the largest input width. -/
theorem densePolynomialFoldFromCosted_length_le (read add multiply : ℕ) (challenge : Fp × ℕ)
    (polys : List (List Fp)) (initial : List Fp) (width : ℕ)
    (hinitial : initial.length ≤ width) (hpolys : ∀ poly ∈ polys, poly.length ≤ width) :
    (densePolynomialFoldFromCosted read add multiply challenge polys initial).1.length ≤ width := by
  induction polys generalizing initial with
  | nil => exact hinitial
  | cons first rest ih =>
    apply ih _
    · rewrite [denseAddCosted_length, denseScaleCosted_length]
      exact max_le hinitial (hpolys first (by simp))
    · exact fun poly hpoly => hpolys poly (List.mem_cons_of_mem first hpoly)

/-- One complete stored Horner step, including the challenge read and retained accumulator. -/
def densePolynomialFoldStepBudget (read add multiply challengeAccess width : ℕ) : ℕ :=
  challengeAccess + width * (read + multiply + 3) + width * (2 * read + add + 2) + read + 6

/-- The complete Horner loop is linear in its member count and stored coefficient width. -/
theorem densePolynomialFoldFromCosted_cost_le (read add multiply : ℕ) (challenge : Fp × ℕ)
    (polys : List (List Fp)) (initial : List Fp) (width : ℕ)
    (hinitial : initial.length ≤ width) (hpolys : ∀ poly ∈ polys, poly.length ≤ width) :
    (densePolynomialFoldFromCosted read add multiply challenge polys initial).2 ≤
      polys.length * densePolynomialFoldStepBudget read add multiply challenge.2 width + 1 := by
  induction polys generalizing initial with
  | nil => simp only [densePolynomialFoldFromCosted, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons first rest ih =>
    have hs := denseScaleCosted_cost_le read multiply challenge initial
    have ha := denseAddCosted_cost_le read add (denseScaleCosted read multiply challenge initial).1 first
    rewrite [denseScaleCosted_length] at ha
    have hnext : (denseAddCosted read add (denseScaleCosted read multiply challenge initial).1 first).1.length ≤ width := by
      rewrite [denseAddCosted_length, denseScaleCosted_length]
      exact max_le hinitial (hpolys first (by simp))
    have hr := ih _ hnext (fun poly hpoly => hpolys poly (List.mem_cons_of_mem first hpoly))
    have hscale := Nat.mul_le_mul_right (read + multiply + 3) hinitial
    have hadd := Nat.mul_le_mul_right (2 * read + add + 2) hinitial
    change _ + _ + _ + read + 3 ≤ _
    rewrite [List.length_cons, Nat.add_mul, Nat.one_mul]
    unfold densePolynomialFoldStepBudget at *
    omega

/-- Construct the source's polynomial fold from zero. -/
def densePolynomialFoldCosted (read add multiply : ℕ) (challenge : Fp × ℕ)
    (polys : List (List Fp)) : List Fp × ℕ :=
  densePolynomialFoldFromCosted read add multiply challenge polys []

/-- Cost erasure gives the original fold, including its zero-challenge behavior. -/
theorem densePolynomialFoldCosted_result (read add multiply : ℕ) (challenge : Fp × ℕ)
    (polys : List (List Fp)) :
    densePolynomial (densePolynomialFoldCosted read add multiply challenge polys).1 =
      plonkPolynomialFold challenge.1 (polys.map densePolynomial) :=
  densePolynomialFoldFromCosted_result read add multiply challenge polys []

/-- Every folded polynomial fits the common input capacity. -/
theorem densePolynomialFoldCosted_length_le (read add multiply : ℕ) (challenge : Fp × ℕ)
    (polys : List (List Fp)) (width : ℕ) (hpolys : ∀ poly ∈ polys, poly.length ≤ width) :
    (densePolynomialFoldCosted read add multiply challenge polys).1.length ≤ width :=
  densePolynomialFoldFromCosted_length_le read add multiply challenge polys [] width (Nat.zero_le _) hpolys

/-- Complete source-fold cost; there is no unpriced polynomial operation. -/
theorem densePolynomialFoldCosted_cost_le (read add multiply : ℕ) (challenge : Fp × ℕ)
    (polys : List (List Fp)) (width : ℕ) (hpolys : ∀ poly ∈ polys, poly.length ≤ width) :
    (densePolynomialFoldCosted read add multiply challenge polys).2 ≤
      polys.length * densePolynomialFoldStepBudget read add multiply challenge.2 width + 1 :=
  densePolynomialFoldFromCosted_cost_le read add multiply challenge polys [] width (Nat.zero_le _) hpolys

end Zcash.Snark.ZeroKnowledge
