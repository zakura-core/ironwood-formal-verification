import Zcash.Snark.ZeroKnowledge.MonicQuotientComposition

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- The polynomial product specified by an ordered list of linear factors. -/
def denseRootDivisor (roots : List Fp) : CPoly :=
  (roots.map fun root => CPolynomial.X - CPolynomial.C root).prod

/-- Every linear-factor product is monic, including repeated roots and the empty product. -/
theorem denseRootDivisor_monic (roots : List Fp) : (denseRootDivisor roots).toPoly.Monic := by
  induction roots with
  | nil => simp [denseRootDivisor, CPolynomial.toPoly_one]
  | cons root rest ih =>
    change ((CPolynomial.X - CPolynomial.C root) * denseRootDivisor rest).toPoly.Monic
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
    exact (Polynomial.monic_X_sub_C root).mul ih

/-- Divide successively by stored linear factors, counting every pass and root read. -/
def denseDivRootsCosted (read add multiply : ℕ) : List Fp → List Fp → List Fp × ℕ
  | [], values => (values, 1)
  | root :: rest, values =>
    let first := denseDivLinearCosted read add multiply (root, read + 1) values
    let later := denseDivRootsCosted read add multiply rest first.1
    (later.1, first.2 + later.2 + 2)

/-- Successive stored divisions recover the original quotient by the full factor product. -/
theorem denseDivRootsCosted_result (read add multiply : ℕ) (roots values : List Fp) :
    densePolynomial (denseDivRootsCosted read add multiply roots values).1 =
      (densePolynomial values).div (denseRootDivisor roots) := by
  induction roots generalizing values with
  | nil =>
    apply CPolynomial.toPoly_injective
    simp only [denseDivRootsCosted, denseRootDivisor, List.map_nil, List.prod_nil,
      CPolynomial.div_toPoly_eq_div, CPolynomial.toPoly_one, EuclideanDomain.div_one]
  | cons root rest ih =>
    dsimp only [denseDivRootsCosted]
    rw [ih, denseDivLinearCosted_result]
    have hm : (CPolynomial.X - CPolynomial.C root : CPoly).toPoly.Monic := by
      rw [CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
      exact Polynomial.monic_X_sub_C root
    rw [cPolynomial_div_product_monic _ _ _ hm (denseRootDivisor_monic rest)]
    rfl

/-- Successive divisions retain the fixed input width on every branch. -/
theorem denseDivRootsCosted_length (read add multiply : ℕ) (roots values : List Fp) :
    (denseDivRootsCosted read add multiply roots values).1.length = values.length := by
  induction roots generalizing values with
  | nil => rfl
  | cons root rest ih => simp only [denseDivRootsCosted, ih, denseDivLinearCosted_length]

/-- Exact complete runtime for all linear-factor passes. -/
theorem denseDivRootsCosted_cost (read add multiply : ℕ) (roots values : List Fp) :
    (denseDivRootsCosted read add multiply roots values).2 =
      roots.length * (values.length * (read + add + multiply + 5) + read + 5) + 1 := by
  induction roots generalizing values with
  | nil => simp [denseDivRootsCosted]
  | cons root rest ih =>
    simp only [denseDivRootsCosted, ih, denseDivLinearCosted_length, denseDivLinearCosted_cost,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end Zcash.Snark.ZeroKnowledge
