import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost
import Zcash.Snark.ZeroKnowledge.PolynomialCommitment

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark CompPoly

/-- Read a materialized coefficient array, including the original zero default outside its size. -/
def polynomialCoeffCosted {F : Type*} [Zero F] (elementRead : ℕ)
    (poly : CPolynomial F) (index : ℕ) : F × ℕ :=
  if h : index < poly.val.size then (poly.val[index], elementRead + 2) else (0, 2)

/-- Cost erasure is exactly the original canonical polynomial coefficient access. -/
theorem polynomialCoeffCosted_result {F : Type*} [Zero F] (elementRead : ℕ)
    (poly : CPolynomial F) (index : ℕ) :
    (polynomialCoeffCosted elementRead poly index).1 = poly.coeff index := by
  by_cases h : index < poly.val.size <;>
    simp [polynomialCoeffCosted, CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD, h]

/-- Both in-range and default-zero reads fit the same explicit array-access bound. -/
theorem polynomialCoeffCosted_cost_le {F : Type*} [Zero F] (elementRead : ℕ)
    (poly : CPolynomial F) (index : ℕ) :
    (polynomialCoeffCosted elementRead poly index).2 ≤ elementRead + 2 := by
  unfold polynomialCoeffCosted
  split <;> omega

/-- Materialize the actual coefficient array while charging each read and list cell. -/
def polynomialArrayCosted {F : Type*} [Zero F] (elementRead : ℕ)
    (poly : CPolynomial F) : List F × ℕ :=
  ofFnCosted (count := poly.val.size) fun index => (poly.val[index.val], elementRead + 1)

/-- The materialized coefficients are exactly the stored canonical array in its original order. -/
theorem polynomialArrayCosted_result {F : Type*} [Zero F] (elementRead : ℕ)
    (poly : CPolynomial F) :
    (polynomialArrayCosted elementRead poly).1 = poly.val.toList := by
  rw [polynomialArrayCosted, ofFnCosted_result]
  refine List.ext_getElem (by simp) ?_
  intro index hleft hright
  simp

/-- Coefficient-array materialization includes all input reads and index adapters. -/
theorem polynomialArrayCosted_cost_le {F : Type*} [Zero F] (elementRead : ℕ)
    (poly : CPolynomial F) :
    (polynomialArrayCosted elementRead poly).2 ≤
      poly.val.size * (elementRead + 2) + poly.val.size * poly.val.size + 1 := by
  exact ofFnCosted_cost_le (fun index : Fin poly.val.size => (poly.val[index.val], elementRead + 1))
    (elementRead + 1) (fun _ => le_rfl)

/-- Horner evaluation of a materialized coefficient list with explicit read and arithmetic costs. -/
def listHornerCosted {F : Type*} [Semiring F] (elementRead add multiply : ℕ)
    (point : F × ℕ) : List F → F × ℕ
  | [] => (0, 1)
  | first :: rest =>
    let upper := listHornerCosted elementRead add multiply point rest
    (upper.1 * point.1 + first, upper.2 + point.2 + elementRead + add + multiply + 1)

/-- Erasing Horner costs gives the exact coefficient-order right fold. -/
theorem listHornerCosted_result {F : Type*} [Semiring F] (elementRead add multiply : ℕ)
    (point : F × ℕ) (values : List F) :
    (listHornerCosted elementRead add multiply point values).1 =
      values.foldr (fun coefficient upper => upper * point.1 + coefficient) 0 := by
  induction values <;> simp_all only [listHornerCosted, List.foldr_nil, List.foldr_cons]

/-- Exact cost of the materialized Horner loop, including its empty-list case. -/
theorem listHornerCosted_cost {F : Type*} [Semiring F] (elementRead add multiply : ℕ)
    (point : F × ℕ) (values : List F) :
    (listHornerCosted elementRead add multiply point values).2 =
      values.length * (point.2 + elementRead + add + multiply + 1) + 1 := by
  induction values with
  | nil => simp [listHornerCosted]
  | cons first rest ih =>
    simp only [listHornerCosted, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Evaluate the actual canonical polynomial with a counted, materialized Horner implementation. -/
def polynomialEvalCosted {F : Type*} [Semiring F] (arrayRead listRead add multiply : ℕ)
    (poly : CPolynomial F) (point : F × ℕ) : F × ℕ :=
  let coefficients := polynomialArrayCosted arrayRead poly
  let value := listHornerCosted listRead add multiply point coefficients.1
  (value.1, coefficients.2 + value.2 + 1)

/-- The counted algorithm has exactly the evaluation used by the existing prover. -/
theorem polynomialEvalCosted_result {F : Type*} [Semiring F] (arrayRead listRead add multiply : ℕ)
    (poly : CPolynomial F) (point : F × ℕ) :
    (polynomialEvalCosted arrayRead listRead add multiply poly point).1 = poly.eval point.1 := by
  simp only [polynomialEvalCosted, listHornerCosted_result, polynomialArrayCosted_result]
  calc
    _ = CPolynomial.evalHorner point.1 poly := by
      rw [Array.foldr_toList]
      rfl
    _ = _ := CPolynomial.eval_horner_eq_eval point.1 poly

/-- The evaluation bound includes constructing and reading every coefficient. -/
theorem polynomialEvalCosted_cost_le {F : Type*} [Semiring F] (arrayRead listRead add multiply : ℕ)
    (poly : CPolynomial F) (point : F × ℕ) :
    (polynomialEvalCosted arrayRead listRead add multiply poly point).2 ≤
      poly.val.size * (arrayRead + listRead + point.2 + add + multiply + 3) +
        poly.val.size * poly.val.size + 3 := by
  have harray := polynomialArrayCosted_cost_le arrayRead poly
  have hhorner := listHornerCosted_cost listRead add multiply point (polynomialArrayCosted arrayRead poly).1
  have hlength : (polynomialArrayCosted arrayRead poly).1.length = poly.val.size := by
    rw [polynomialArrayCosted_result, Array.length_toList]
  rw [hlength] at hhorner
  dsimp only [polynomialEvalCosted]
  calc
    _ ≤ (poly.val.size * (arrayRead + 2) + poly.val.size * poly.val.size + 1) +
        (poly.val.size * (point.2 + listRead + add + multiply + 1) + 1) + 1 := by omega
    _ = _ := by ring

end Zcash.Snark.ZeroKnowledge
