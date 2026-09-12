import Zcash.Snark.ZeroKnowledge.CommitmentCoefficientRoutingCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Full private slot routing includes both source schedule constructions and polynomial lookup. -/
def privateCommitmentCoefficientCostBudget (equal read actions columns : ℕ) : ℕ :=
  4 * actions * actions + 304 * actions + read + 14 +
    privateColumnCoefficientsCostBudget equal read actions columns + 1

/-- Bound the actual index-to-identity-to-polynomial route. -/
theorem privateCommitmentCoefficientCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (columns : List (List Fp)) (index : Fin (22 * actions)) :
    (privateCommitmentCoefficientCosted equal read columns index).2 ≤
      privateCommitmentCoefficientCostBudget equal read actions columns.length := by
  have hi := privateColumnAtCosted_cost_le read index
  have hp := privateColumnCoefficientsCosted_cost_le equal read columns (privateColumnAtCosted read index).1
  change (privateColumnAtCosted read index).2 +
    (privateColumnCoefficientsCosted equal read columns (privateColumnAtCosted read index).1).2 + 1 ≤ _
  unfold privateCommitmentCoefficientCostBudget
  omega

/-- A common price covers every original commitment slot and its routing branches. -/
def plonkCommitmentCoefficientCostBudget (equal read actions columns pieces linearRead quotientRead : ℕ) : ℕ :=
  privateCommitmentCoefficientCostBudget equal read actions columns +
    (2 * pieces + read + 1) + linearRead + quotientRead + 6

/-- All private and shared commitment-slot readers have the stated complete bound. -/
theorem plonkCommitmentCoefficientCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (columns pieces : List (List Fp)) (linear quotientPrime : List Fp × ℕ)
    (index : Fin (22 * actions + 10)) :
    (plonkCommitmentCoefficientCosted equal read columns pieces linear quotientPrime index).2 ≤
      plonkCommitmentCoefficientCostBudget equal read actions columns.length pieces.length linear.2 quotientPrime.2 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · have h := privateCommitmentCoefficientCosted_cost_le equal read columns i
    simp only [plonkCommitmentCoefficientCosted, Fin.append_left, plonkCommitmentCoefficientCostBudget]
    omega
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_zero, plonkCommitmentCoefficientCostBudget]
      omega
    · refine Fin.addCases (m := 8) (n := 1) (fun j => ?_) (fun j => ?_) i
      · have h := getDListCosted_cost_le read ([] : List Fp) pieces j.val
        simp only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_succ, Fin.append_left,
          plonkCommitmentCoefficientCostBudget]
        omega
      · simp only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_succ, plonkCommitmentCoefficientCostBudget]
        omega

/-- The complete routing preserves a common stored-polynomial capacity. -/
theorem plonkCommitmentCoefficientCosted_width (equal read : ℕ) {actions : ℕ}
    (columns pieces : List (List Fp)) (linear quotientPrime : List Fp × ℕ) (width : ℕ)
    (hc : ∀ poly ∈ columns, poly.length ≤ width) (hp : ∀ poly ∈ pieces, poly.length ≤ width)
    (hl : linear.1.length ≤ width) (hq : quotientPrime.1.length ≤ width)
    (index : Fin (22 * actions + 10)) :
    (plonkCommitmentCoefficientCosted equal read columns pieces linear quotientPrime index).1.length ≤ width := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · simp only [plonkCommitmentCoefficientCosted, Fin.append_left, privateCommitmentCoefficientCosted]
    exact privateColumnCoefficientsCosted_length_le equal read columns (privateColumnAtCosted read i).1 width hc
  · refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_zero] using hl
    · refine Fin.addCases (m := 8) (n := 1) (fun j => ?_) (fun j => ?_) i
      · simp only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_succ, Fin.append_left]
        exact getDListCosted_property read [] pieces (fun poly => poly.length ≤ width) (Nat.zero_le _) hp j.val
      · simpa only [plonkCommitmentCoefficientCosted, Fin.append_right, Fin.cons_succ] using hq

end Zcash.Snark.ZeroKnowledge
