import Zcash.Snark.ZeroKnowledge.DensePolynomial

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Sum stored polynomials while retaining each coefficient addition and list read. -/
def densePolynomialSumCosted (read add : ℕ) : List (List Fp) → List Fp × ℕ
  | [] => ([], 1)
  | first :: rest =>
    let tail := densePolynomialSumCosted read add rest
    let result := denseAddCosted read add first tail.1
    (result.1, tail.2 + result.2 + read + 2)

/-- Erasure is the exact polynomial sum, including empty and zero-padded lists. -/
theorem densePolynomialSumCosted_result (read add : ℕ) (polys : List (List Fp)) :
    densePolynomial (densePolynomialSumCosted read add polys).1 = (polys.map densePolynomial).sum := by
  induction polys with
  | nil => rfl
  | cons first rest ih =>
    simp only [densePolynomialSumCosted, denseAddCosted_result, ih, List.map_cons, List.sum_cons]

/-- The sum retains at most the largest supplied storage width. -/
theorem densePolynomialSumCosted_length_le (read add : ℕ) (polys : List (List Fp))
    (width : ℕ) (hpolys : ∀ poly ∈ polys, poly.length ≤ width) :
    (densePolynomialSumCosted read add polys).1.length ≤ width := by
  induction polys with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
    change (denseAddCosted read add first (densePolynomialSumCosted read add rest).1).1.length ≤ width
    rewrite [denseAddCosted_length]
    exact max_le (hpolys first (by simp)) (ih (fun poly hpoly => hpolys poly (List.mem_cons_of_mem first hpoly)))

/-- The sum's full counter is polynomial in member count and coefficient width. -/
theorem densePolynomialSumCosted_cost_le (read add : ℕ) (polys : List (List Fp))
    (width : ℕ) (hpolys : ∀ poly ∈ polys, poly.length ≤ width) :
    (densePolynomialSumCosted read add polys).2 ≤
      polys.length * (width * (2 * read + add + 2) + read + 3) + 1 := by
  induction polys with
  | nil => simp only [densePolynomialSumCosted, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons first rest ih =>
    have hr := ih (fun poly hpoly => hpolys poly (List.mem_cons_of_mem first hpoly))
    have ha := denseAddCosted_cost_le read add first (densePolynomialSumCosted read add rest).1
    have hw := Nat.mul_le_mul_right (2 * read + add + 2) (hpolys first (by simp))
    change _ + _ + read + 2 ≤ _
    rewrite [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end Zcash.Snark.ZeroKnowledge
