import Zcash.Snark.ZeroKnowledge.PolynomialArithmeticCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost

/-!+# Counted public commitments and Horner folds

Coefficient commitments enumerate the actual generator vector and read the
canonical polynomial's stored coefficient array, retaining its zero default.
All supplied generator and polynomial-access costs are retained. Horner folds
charge each materialized input, challenge access, and arithmetic operation.
These are structural costs with explicit prices for field and group primitives;
constructing the input arrays and lists is charged by the surrounding algorithm.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark CompPoly
open Zcash.Arithmetic (Fp)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Count the complete coefficient commitment, including its independent blinding term. -/
def polynomialCommitmentCosted (arrayRead groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (W : G × ℕ) (poly : CPoly × ℕ) (blind : Fp × ℕ) : G × ℕ :=
  let coefficients := sumFinCosted groupAdd fun index =>
    let generator := generators index
    let coefficient := polynomialCoeffCosted arrayRead poly.1 index.val
    (coefficient.1 • generator.1, coefficient.2 + generator.2 + groupScale + 1)
  (coefficients.1 + blind.1 • W.1,
    poly.2 + coefficients.2 + blind.2 + W.2 + groupScale + groupAdd + 1)

/-- Erasing costs gives exactly the coefficient and blinding commitment already used by PLONK. -/
theorem polynomialCommitmentCosted_result (arrayRead groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (W : G × ℕ) (poly : CPoly × ℕ) (blind : Fp × ℕ) :
    (polynomialCommitmentCosted arrayRead groupAdd groupScale generators W poly blind).1 =
      polynomialCommitment (fun index => (generators index).1) W.1 poly.1 blind.1 := by
  simp only [polynomialCommitmentCosted, sumFinCosted_result, polynomialCoeffCosted_result,
    polynomialCommitment, commitGen, polynomialCoefficients]

/-- The full generator sweep is bounded independently of the polynomial's values and degree. -/
theorem polynomialCommitmentCosted_cost_le (arrayRead groupAdd groupScale : ℕ) {n : ℕ}
    (generators : Fin n → G × ℕ) (W : G × ℕ) (poly : CPoly × ℕ) (blind : Fp × ℕ)
    (generatorRead : ℕ) (hread : ∀ index, (generators index).2 ≤ generatorRead) :
    (polynomialCommitmentCosted arrayRead groupAdd groupScale generators W poly blind).2 ≤
      poly.2 + blind.2 + W.2 + n * (arrayRead + generatorRead + groupScale + groupAdd + 4) +
        n * n + groupScale + groupAdd + 2 := by
  have hentry (index : Fin n) :
      (polynomialCoeffCosted arrayRead poly.1 index.val).2 + (generators index).2 + groupScale + 1 ≤
        arrayRead + generatorRead + groupScale + 3 := by
    have hc := polynomialCoeffCosted_cost_le arrayRead poly.1 index.val
    have hg := hread index
    omega
  have hsum := sumFinCosted_cost_le groupAdd (fun index : Fin n =>
      ((polynomialCoeffCosted arrayRead poly.1 index.val).1 • (generators index).1,
        (polynomialCoeffCosted arrayRead poly.1 index.val).2 + (generators index).2 + groupScale + 1))
    (arrayRead + generatorRead + groupScale + 3) hentry
  dsimp only [polynomialCommitmentCosted]
  calc
    _ ≤ poly.2 +
        (n * (arrayRead + generatorRead + groupScale + 3 + groupAdd + 1) + n * n + 1) +
        blind.2 + W.2 + groupScale + groupAdd + 1 := by omega
    _ = _ := by ring

/-- Count the existing Horner fold of materialized commitment points. -/
def commitmentHornerFoldCosted (groupAdd groupScale : ℕ) (challenge : Fp × ℕ)
    (points : List (G × ℕ)) : G × ℕ :=
  foldlCosted (fun state point =>
    (challenge.1 • state + point.1, challenge.2 + point.2 + groupScale + groupAdd + 1)) points (0, 1)

/-- The counted fold preserves the exact commitment order and public challenge. -/
theorem commitmentHornerFoldCosted_result (groupAdd groupScale : ℕ) (challenge : Fp × ℕ)
    (points : List (G × ℕ)) :
    (commitmentHornerFoldCosted groupAdd groupScale challenge points).1 =
      commitmentHornerFold challenge.1 (points.map Prod.fst) := by
  simp only [commitmentHornerFoldCosted, foldlCosted_result, commitmentHornerFold, List.foldl_map]

/-- Every input point and group operation is charged throughout the commitment fold. -/
theorem commitmentHornerFoldCosted_cost_le (groupAdd groupScale : ℕ) (challenge : Fp × ℕ)
    (points : List (G × ℕ)) (pointRead : ℕ) (hread : ∀ point ∈ points, point.2 ≤ pointRead) :
    (commitmentHornerFoldCosted groupAdd groupScale challenge points).2 ≤
      points.length * (challenge.2 + pointRead + groupScale + groupAdd + 2) + 2 := by
  have h := foldlCosted_cost_le_sum (fun state (point : G × ℕ) =>
      (challenge.1 • state + point.1, challenge.2 + point.2 + groupScale + groupAdd + 1))
    points (0, 1) (fun _ => True) (fun _ => challenge.2 + pointRead + groupScale + groupAdd + 1)
    trivial (fun _ _ _ _ => trivial) (fun _ _ point hpoint => by
      have hr := hread point hpoint
      dsimp only
      omega)
  have hsum :
      (points.map (fun _ => challenge.2 + pointRead + groupScale + groupAdd + 1)).sum =
        points.length * (challenge.2 + pointRead + groupScale + groupAdd + 1) := by simp
  rw [hsum] at h
  dsimp only [commitmentHornerFoldCosted]
  calc
    _ ≤ 1 + points.length * (challenge.2 + pointRead + groupScale + groupAdd + 1) + points.length + 1 := h
    _ = _ := by ring

/-- Count the scalar Horner fold used for PLONK's opening claims. -/
def plonkScalarFoldCosted (add multiply : ℕ) (challenge : Fp × ℕ)
    (values : List (Fp × ℕ)) : Fp × ℕ :=
  foldlCosted (fun state value =>
    (state * challenge.1 + value.1, challenge.2 + value.2 + multiply + add + 1)) values (0, 1)

/-- The counted scalar fold has exactly the original ordered claim value. -/
theorem plonkScalarFoldCosted_result (add multiply : ℕ) (challenge : Fp × ℕ)
    (values : List (Fp × ℕ)) :
    (plonkScalarFoldCosted add multiply challenge values).1 =
      plonkScalarFold challenge.1 (values.map Prod.fst) := by
  simp only [plonkScalarFoldCosted, foldlCosted_result, plonkScalarFold, List.foldl_map]

/-- The scalar fold retains complete input accesses and all field operations. -/
theorem plonkScalarFoldCosted_cost_le (add multiply : ℕ) (challenge : Fp × ℕ)
    (values : List (Fp × ℕ)) (valueRead : ℕ) (hread : ∀ value ∈ values, value.2 ≤ valueRead) :
    (plonkScalarFoldCosted add multiply challenge values).2 ≤
      values.length * (challenge.2 + valueRead + multiply + add + 2) + 2 := by
  have h := foldlCosted_cost_le_sum (fun state (value : Fp × ℕ) =>
      (state * challenge.1 + value.1, challenge.2 + value.2 + multiply + add + 1))
    values (0, 1) (fun _ => True) (fun _ => challenge.2 + valueRead + multiply + add + 1)
    trivial (fun _ _ _ _ => trivial) (fun _ _ value hvalue => by
      have hr := hread value hvalue
      dsimp only
      omega)
  have hsum : (values.map (fun _ => challenge.2 + valueRead + multiply + add + 1)).sum =
      values.length * (challenge.2 + valueRead + multiply + add + 1) := by simp
  rw [hsum] at h
  dsimp only [plonkScalarFoldCosted]
  calc
    _ ≤ 1 + values.length * (challenge.2 + valueRead + multiply + add + 1) + values.length + 1 := h
    _ = _ := by ring

end Zcash.Snark.ZeroKnowledge
