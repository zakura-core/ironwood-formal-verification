import Zcash.Snark.ZeroKnowledge.PrivateColumnAtCost
import Zcash.Snark.ZeroKnowledge.PrivateCoefficientRoutingCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Follow the original index-to-identity-to-column routing, counting both schedule traversals. -/
def privateCommitmentCoefficientCosted (equal read : ℕ) {actions : ℕ}
    (columns : List (List Fp)) (index : Fin (22 * actions)) : List Fp × ℕ :=
  let id := privateColumnAtCosted read index
  let poly := privateColumnCoefficientsCosted equal read columns id.1
  (poly.1, id.2 + poly.2 + 1)

/-- A private commitment uses precisely the source's identity-selected polynomial. -/
theorem privateCommitmentCoefficientCosted_result (equal read : ℕ) {actions : ℕ}
    (columns : List (List Fp)) (index : Fin (22 * actions)) :
    densePolynomial (privateCommitmentCoefficientCosted equal read columns index).1 =
      (columns.map densePolynomial).getD ((privateColumnOrder actions).idxOf (privateColumnAt index)) 0 := by
  simp only [privateCommitmentCoefficientCosted, privateColumnCoefficientsCosted_result, privateColumnAtCosted_result]

/-- Route the actual private columns, linear mask, eight pieces, and quotient-prime in their original positions. -/
def plonkCommitmentCoefficientCosted (equal read : ℕ) {actions : ℕ}
    (columns pieces : List (List Fp)) (linear quotientPrime : List Fp × ℕ)
    (index : Fin (22 * actions + 10)) : List Fp × ℕ :=
  let selected := Fin.append (privateCommitmentCoefficientCosted equal read columns)
    (Fin.cons linear (Fin.append (fun index : Fin 8 => getDListCosted read [] pieces index.val)
      (fun _ : Fin 1 => quotientPrime))) index
  (selected.1, selected.2 + 6)

/-- Routing erasure preserves every original slot, including defaulted private and piece reads. -/
theorem plonkCommitmentCoefficientCosted_result (equal read : ℕ) {actions : ℕ}
    (columns pieces : List (List Fp)) (linear quotientPrime : List Fp × ℕ)
    (index : Fin (22 * actions + 10)) :
    densePolynomial (plonkCommitmentCoefficientCosted equal read columns pieces linear quotientPrime index).1 =
      Fin.append
        (fun i => (columns.map densePolynomial).getD ((privateColumnOrder actions).idxOf (privateColumnAt i)) 0)
        (Fin.cons (densePolynomial linear.1)
          (Fin.append (fun i : Fin 8 => densePolynomial (pieces.getD i.val []))
            (fun _ : Fin 1 => densePolynomial quotientPrime.1))) index := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · simp only [plonkCommitmentCoefficientCosted, Fin.append_left, privateCommitmentCoefficientCosted_result]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_zero]
    · refine Fin.addCases (m := 8) (n := 1) (fun j => ?_) (fun j => ?_) i
      · simp only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_succ, Fin.append_left,
          getDListCosted_result]
      · simp only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_succ]

/-- Constructed row coefficients discharge the private-polynomial source premises of the routing. -/
theorem plonkCommitmentCoefficientCosted_from_rows (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ} (rows : List (Fin 2048 → Fp × ℕ))
    (pieces : List (List Fp)) (linear quotientPrime : List Fp × ℕ)
    (index : Fin (22 * actions + 10)) :
    densePolynomial (plonkCommitmentCoefficientCosted equal read
      (privatePolynomialCoefficientsCosted costs (Zcash.Arithmetic.omegaOf 11, omegaAccess) rows).1
      pieces linear quotientPrime index).1 =
      Fin.append (fun i => privateColumnPolynomial (rows.map (fun column row => (column row).1)) (privateColumnAt i))
        (Fin.cons (densePolynomial linear.1)
          (Fin.append (fun i : Fin 8 => densePolynomial (pieces.getD i.val []))
            (fun _ : Fin 1 => densePolynomial quotientPrime.1))) index := by
  rewrite [plonkCommitmentCoefficientCosted_result,
    privatePolynomialCoefficientsCosted_result costs 11 (by decide) omegaAccess]
  simp only [privateColumnPolynomial, List.map_map, Function.comp_def]
  rfl

end Zcash.Snark.ZeroKnowledge
