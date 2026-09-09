import Zcash.Snark.ZeroKnowledge.CommitmentCoefficientRoutingBound
import Zcash.Snark.ZeroKnowledge.DenseCommitmentCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Materialize every original pre-IPA commitment, including its same-slot private blind. -/
def plonkCommitmentPointsCosted (equal read groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (columns pieces : List (List Fp))
    (linear quotientPrime : List Fp × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ) : List G × ℕ :=
  ofFnCosted fun index => densePolynomialCommitmentCosted read groupAdd groupScale generators W
    (plonkCommitmentCoefficientCosted equal read columns pieces linear quotientPrime index) (blinds index)

/-- Every materialized point has the original stored polynomial and its same-position blind. -/
theorem plonkCommitmentPointsCosted_result (equal read groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (columns pieces : List (List Fp))
    (linear quotientPrime : List Fp × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ) :
    (plonkCommitmentPointsCosted equal read groupAdd groupScale generators W columns pieces linear quotientPrime blinds).1 =
      List.ofFn (fun index => polynomialCommitment (fun i => (generators i).1) W.1
        (densePolynomial (plonkCommitmentCoefficientCosted equal read columns pieces linear quotientPrime index).1)
        (blinds index).1) := by
  simp only [plonkCommitmentPointsCosted, ofFnCosted_result, densePolynomialCommitmentCosted_result]

/-- Exactly every original commitment slot is forced into the output list. -/
theorem plonkCommitmentPointsCosted_length (equal read groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (columns pieces : List (List Fp))
    (linear quotientPrime : List Fp × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ) :
    (plonkCommitmentPointsCosted equal read groupAdd groupScale generators W columns pieces linear quotientPrime blinds).1.length =
      22 * actions + 10 := ofFnCosted_length _

/-- Complete full-vector commitment budget, including all slot routing and stored coefficient traversal. -/
def plonkCommitmentPointsCostBudget
    (equal read groupAdd groupScale actions columns pieces width generatorRead entryRead linearRead quotientRead wRead : ℕ) : ℕ :=
  (22 * actions + 10) * (densePolynomialCommitmentCostBudget read groupAdd groupScale 2048 width generatorRead
    (plonkCommitmentCoefficientCostBudget equal read actions columns pieces linearRead quotientRead) entryRead wRead + 1) +
    (22 * actions + 10) * (22 * actions + 10) + 1

/-- Capacity and reader bounds cover every actual pre-IPA point computation. -/
theorem plonkCommitmentPointsCosted_cost_le (equal read groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (columns pieces : List (List Fp))
    (linear quotientPrime : List Fp × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (width generatorRead entryRead : ℕ) (hc : ∀ poly ∈ columns, poly.length ≤ width)
    (hp : ∀ poly ∈ pieces, poly.length ≤ width) (hl : linear.1.length ≤ width) (hq : quotientPrime.1.length ≤ width)
    (hg : ∀ i, (generators i).2 ≤ generatorRead) (hb : ∀ i, (blinds i).2 ≤ entryRead) :
    (plonkCommitmentPointsCosted equal read groupAdd groupScale generators W columns pieces linear quotientPrime blinds).2 ≤
      plonkCommitmentPointsCostBudget equal read groupAdd groupScale actions columns.length pieces.length width
        generatorRead entryRead linear.2 quotientPrime.2 W.2 := by
  unfold plonkCommitmentPointsCosted plonkCommitmentPointsCostBudget
  apply ofFnCosted_cost_le
  intro index
  have h := densePolynomialCommitmentCosted_cost_le read groupAdd groupScale generators W
    (plonkCommitmentCoefficientCosted equal read columns pieces linear quotientPrime index) (blinds index) generatorRead hg
  have hw := plonkCommitmentCoefficientCosted_width equal read columns pieces linear quotientPrime width hc hp hl hq index
  have hr := plonkCommitmentCoefficientCosted_cost_le equal read columns pieces linear quotientPrime index
  have he := hb index
  refine h.trans ?_
  unfold densePolynomialCommitmentCostBudget
  gcongr

end Zcash.Snark.ZeroKnowledge
