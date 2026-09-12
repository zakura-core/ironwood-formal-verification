import Zcash.Snark.ZeroKnowledge.DensePolynomial

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Scale stored coefficients, retaining scalar preparation even for the empty polynomial. -/
def denseScaleCosted (read multiply : ℕ) (scalar : Fp × ℕ) (values : List Fp) : List Fp × ℕ :=
  let result := mapListCosted (fun value => (scalar.1 * value, read + multiply + 2)) values
  (result.1, scalar.2 + result.2 + 1)

/-- Pointwise coefficient scaling is the existing constant-polynomial multiplication. -/
theorem denseScaleCosted_result (read multiply : ℕ) (scalar : Fp × ℕ) (values : List Fp) :
    densePolynomial (denseScaleCosted read multiply scalar values).1 =
      CPolynomial.C scalar.1 * densePolynomial values := by
  simp only [denseScaleCosted, mapListCosted_result]
  induction values with
  | nil => simp [densePolynomial]
  | cons first rest ih =>
    simp only [List.map_cons, densePolynomial, ih, CPolynomial.C_mul]
    ring

/-- Scaling preserves the entire stored width, including zero coefficients. -/
theorem denseScaleCosted_length (read multiply : ℕ) (scalar : Fp × ℕ) (values : List Fp) :
    (denseScaleCosted read multiply scalar values).1.length = values.length := by
  simp only [denseScaleCosted, mapListCosted_result, List.length_map]

/-- Complete scaling cost includes the prepared scalar and every stored coefficient. -/
theorem denseScaleCosted_cost_le (read multiply : ℕ) (scalar : Fp × ℕ) (values : List Fp) :
    (denseScaleCosted read multiply scalar values).2 ≤
      scalar.2 + values.length * (read + multiply + 3) + 2 := by
  have h := mapListCosted_cost_le (fun value : Fp => (scalar.1 * value, read + multiply + 2))
    values (read + multiply + 2) (by simp)
  rw [show read + multiply + 2 + 1 = read + multiply + 3 by omega] at h
  dsimp only [denseScaleCosted]
  omega

/-- Negate the stored coefficients with an explicit field-operation counter. -/
def denseNegCosted (read negate : ℕ) (values : List Fp) : List Fp × ℕ :=
  mapListCosted (fun value => (-value, read + negate + 1)) values

/-- The counted negation has the original polynomial meaning. -/
theorem denseNegCosted_result (read negate : ℕ) (values : List Fp) :
    densePolynomial (denseNegCosted read negate values).1 = -densePolynomial values := by
  simp only [denseNegCosted, mapListCosted_result]
  induction values with
  | nil => simp [densePolynomial]
  | cons first rest ih =>
    have hc : CPolynomial.C (-first) = -CPolynomial.C first := by
      apply eq_neg_of_add_eq_zero_left
      rw [← CPolynomial.C_add, neg_add_cancel, CPolynomial.C_zero]
    simp only [List.map_cons, densePolynomial, ih, hc]
    ring

/-- Negation preserves every stored coefficient slot. -/
theorem denseNegCosted_length (read negate : ℕ) (values : List Fp) :
    (denseNegCosted read negate values).1.length = values.length := by
  simp only [denseNegCosted, mapListCosted_result, List.length_map]

/-- The complete negation loop is linear in its materialized width. -/
theorem denseNegCosted_cost_le (read negate : ℕ) (values : List Fp) :
    (denseNegCosted read negate values).2 ≤ values.length * (read + negate + 2) + 1 :=
  mapListCosted_cost_le _ _ (read + negate + 1) (by simp)

end Zcash.Snark.ZeroKnowledge
