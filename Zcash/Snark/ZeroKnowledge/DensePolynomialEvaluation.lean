import Zcash.Snark.ZeroKnowledge.DensePolynomial
import Zcash.Snark.ZeroKnowledge.PolynomialArithmeticCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- The stored-coefficient Horner loop evaluates the decoded polynomial, including trailing zeros. -/
theorem listHornerCosted_densePolynomial_result (read add multiply : ℕ) (point : Fp × ℕ)
    (values : List Fp) :
    (listHornerCosted read add multiply point values).1 = (densePolynomial values).eval point.1 := by
  induction values with
  | nil => simp only [listHornerCosted, densePolynomial, CPolynomial.eval_zero]
  | cons first rest ih =>
    simp only [listHornerCosted, densePolynomial, CPolynomial.eval_add, CPolynomial.eval_C,
      CPolynomial.eval_mul, CPolynomial.eval_X, ih]
    ring

/-- Evaluate a stored polynomial at every original query position without removing duplicates. -/
def densePolynomialNodeValuesCosted (read add multiply : ℕ) (poly points : List Fp) : List Fp × ℕ :=
  mapListCosted (fun point => listHornerCosted read add multiply (point, read + 1) poly) points

/-- The values retain exactly the original node order and multiplicity. -/
theorem densePolynomialNodeValuesCosted_result (read add multiply : ℕ) (poly points : List Fp) :
    (densePolynomialNodeValuesCosted read add multiply poly points).1 =
      points.map (fun point => (densePolynomial poly).eval point) := by
  simp only [densePolynomialNodeValuesCosted, mapListCosted_result, listHornerCosted_densePolynomial_result]

/-- Every original node position has a materialized value. -/
theorem densePolynomialNodeValuesCosted_length (read add multiply : ℕ) (poly points : List Fp) :
    (densePolynomialNodeValuesCosted read add multiply poly points).1.length = points.length := by
  rewrite [densePolynomialNodeValuesCosted_result, List.length_map]
  rfl

/-- The full value vector counts every Horner step, stored coefficient, node read, and output cell. -/
theorem densePolynomialNodeValuesCosted_cost_le (read add multiply : ℕ) (poly points : List Fp) :
    (densePolynomialNodeValuesCosted read add multiply poly points).2 ≤
      points.length * (poly.length * (2 * read + add + multiply + 2) + 2) + 1 := by
  have h := mapListCosted_cost_le
    (fun point : Fp => listHornerCosted read add multiply (point, read + 1) poly) points
    (poly.length * (2 * read + add + multiply + 2) + 1) (by
      intro point _
      rewrite [listHornerCosted_cost]
      have he : (read + 1) + read + add + multiply + 1 = 2 * read + add + multiply + 2 := by omega
      dsimp only
      rewrite [he]
      exact le_rfl)
  exact h

end Zcash.Snark.ZeroKnowledge
