import Zcash.Snark.ZeroKnowledge.DensePolynomialSum
import Zcash.Snark.ZeroKnowledge.DensePolynomialScale

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Prepare one power-weighted polynomial, including the exponent calculation and input producer. -/
def densePowerWeightedTermCosted (read multiply : ℕ) (challenge : Fp × ℕ)
    (stride index : ℕ) (poly : List Fp × ℕ) : List Fp × ℕ :=
  let power := fieldPowerCosted multiply challenge.1 (stride * index)
  let result := denseScaleCosted read multiply (power.1, challenge.2 + power.2 + 2) poly.1
  (result.1, poly.2 + result.2 + 1)

/-- The stored weighted term has exactly its source polynomial meaning. -/
theorem densePowerWeightedTermCosted_result (read multiply : ℕ) (challenge : Fp × ℕ)
    (stride index : ℕ) (poly : List Fp × ℕ) :
    densePolynomial (densePowerWeightedTermCosted read multiply challenge stride index poly).1 =
      CPolynomial.C (challenge.1 ^ (stride * index)) * densePolynomial poly.1 := by
  simp only [densePowerWeightedTermCosted, denseScaleCosted_result, fieldPowerCosted_result]

/-- Weighting preserves all stored coefficient positions. -/
theorem densePowerWeightedTermCosted_length (read multiply : ℕ) (challenge : Fp × ℕ)
    (stride index : ℕ) (poly : List Fp × ℕ) :
    (densePowerWeightedTermCosted read multiply challenge stride index poly).1.length = poly.1.length :=
  denseScaleCosted_length read multiply _ poly.1

/-- Uniform term budget derived from its actual coefficient producer and bounded exponent. -/
theorem densePowerWeightedTermCosted_cost_le (read multiply : ℕ) (challenge : Fp × ℕ)
    (stride index count width access : ℕ) (poly : List Fp × ℕ)
    (hindex : index ≤ count) (hwidth : poly.1.length ≤ width) (haccess : poly.2 ≤ access) :
    (densePowerWeightedTermCosted read multiply challenge stride index poly).2 ≤
      access + challenge.2 + stride * count * (multiply + 1) + width * (read + multiply + 3) + 6 := by
  have hs := denseScaleCosted_cost_le read multiply
    ((fieldPowerCosted multiply challenge.1 (stride * index)).1,
      challenge.2 + (fieldPowerCosted multiply challenge.1 (stride * index)).2 + 2) poly.1
  have hexact := fieldPowerCosted_cost multiply challenge.1 (stride * index)
  have hp := Nat.mul_le_mul_right (multiply + 1) (Nat.mul_le_mul_left stride hindex)
  have hw := Nat.mul_le_mul_right (read + multiply + 3) hwidth
  change poly.2 + _ + 1 ≤ _
  dsimp only at hs
  omega

/-- Construct every weighted coefficient vector and sum it with counted polynomial additions. -/
@[irreducible] def denseWeightedSumCosted (read add multiply : ℕ) (challenge : Fp × ℕ)
    (stride : ℕ) {count : ℕ} (polys : Fin count → List Fp × ℕ) : List Fp × ℕ :=
  let terms := ofFnCosted (fun index => densePowerWeightedTermCosted read multiply challenge stride index.val (polys index))
  let result := densePolynomialSumCosted read add terms.1
  (result.1, terms.2 + result.2 + 1)

/-- The complete routine erases to the exact finite sum of power-weighted polynomials. -/
theorem denseWeightedSumCosted_result (read add multiply : ℕ) (challenge : Fp × ℕ)
    (stride : ℕ) {count : ℕ} (polys : Fin count → List Fp × ℕ) :
    densePolynomial (denseWeightedSumCosted read add multiply challenge stride polys).1 =
      ∑ index, CPolynomial.C (challenge.1 ^ (stride * index.val)) * densePolynomial (polys index).1 := by
  unfold denseWeightedSumCosted
  simp only [densePolynomialSumCosted_result, ofFnCosted_result, List.map_ofFn, Function.comp_def,
    densePowerWeightedTermCosted_result, List.sum_ofFn]

/-- A common coefficient capacity bounds the entire weighted sum. -/
theorem denseWeightedSumCosted_length_le (read add multiply : ℕ) (challenge : Fp × ℕ)
    (stride : ℕ) {count : ℕ} (polys : Fin count → List Fp × ℕ)
    (width : ℕ) (hwidth : ∀ index, (polys index).1.length ≤ width) :
    (denseWeightedSumCosted read add multiply challenge stride polys).1.length ≤ width := by
  unfold denseWeightedSumCosted
  apply densePolynomialSumCosted_length_le
  intro poly hpoly
  simp only [ofFnCosted_result, List.mem_ofFn] at hpoly
  obtain ⟨index, rfl⟩ := hpoly
  rewrite [densePowerWeightedTermCosted_length]
  exact hwidth index

/-- Complete weighted-sum budget, including every input producer, exponent loop, and coefficient. -/
def denseWeightedSumCostBudget (read add multiply challengeAccess stride count width access : ℕ) : ℕ :=
  count * (access + challengeAccess + stride * count * (multiply + 1) + width * (read + multiply + 3) + 7) +
    count * count + count * (width * (2 * read + add + 2) + read + 3) + 3

/-- Every supplied input cost is retained in the complete polynomial sum bound. -/
theorem denseWeightedSumCosted_cost_le (read add multiply : ℕ) (challenge : Fp × ℕ)
    (stride : ℕ) {count : ℕ} (polys : Fin count → List Fp × ℕ) (width access : ℕ)
    (hwidth : ∀ index, (polys index).1.length ≤ width) (haccess : ∀ index, (polys index).2 ≤ access) :
    (denseWeightedSumCosted read add multiply challenge stride polys).2 ≤
      denseWeightedSumCostBudget read add multiply challenge.2 stride count width access := by
  let term := fun index : Fin count => densePowerWeightedTermCosted read multiply challenge stride index.val (polys index)
  have ht := ofFnCosted_cost_le term
    (access + challenge.2 + stride * count * (multiply + 1) + width * (read + multiply + 3) + 6)
    (fun index => densePowerWeightedTermCosted_cost_le read multiply challenge stride index.val count width access
      (polys index) (Nat.le_of_lt index.isLt) (hwidth index) (haccess index))
  rewrite [show access + challenge.2 + stride * count * (multiply + 1) + width * (read + multiply + 3) + 6 + 1 =
    access + challenge.2 + stride * count * (multiply + 1) + width * (read + multiply + 3) + 7 by omega] at ht
  have hterms : ∀ poly ∈ (ofFnCosted term).1, poly.length ≤ width := by
    intro poly hpoly
    simp only [ofFnCosted_result, List.mem_ofFn] at hpoly
    obtain ⟨index, rfl⟩ := hpoly
    exact (densePowerWeightedTermCosted_length read multiply challenge stride index.val (polys index)).le.trans (hwidth index)
  have hs := densePolynomialSumCosted_cost_le read add (ofFnCosted term).1 width hterms
  rewrite [ofFnCosted_length] at hs
  unfold denseWeightedSumCosted
  change (ofFnCosted term).2 + (densePolynomialSumCosted read add (ofFnCosted term).1).2 + 1 ≤ _
  unfold denseWeightedSumCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
