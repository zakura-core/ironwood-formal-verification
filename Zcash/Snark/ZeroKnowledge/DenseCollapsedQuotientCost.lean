import Zcash.Snark.ZeroKnowledge.DenseWeightedSum
import Zcash.Snark.ZeroKnowledge.PlonkOpening

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Collapse all eight stored quotient pieces with the source's exact powers of the evaluation challenge. -/
@[irreducible] def denseCollapsedQuotientCosted (read add multiply : ℕ) (x : Fp × ℕ)
    (pieces : Fin 8 → List Fp × ℕ) : List Fp × ℕ :=
  denseWeightedSumCosted read add multiply x 2048 pieces

/-- Erasure is the actual collapsed quotient, for every evaluation challenge. -/
theorem denseCollapsedQuotientCosted_result (read add multiply : ℕ) (x : Fp × ℕ)
    (pieces : Fin 8 → List Fp × ℕ) :
    densePolynomial (denseCollapsedQuotientCosted read add multiply x pieces).1 =
      plonkCollapsedQuotient x.1 (fun index => densePolynomial (pieces index).1) := by
  unfold denseCollapsedQuotientCosted
  exact denseWeightedSumCosted_result read add multiply x 2048 pieces

/-- Collapsing pieces preserves their common stored capacity. -/
theorem denseCollapsedQuotientCosted_length_le (read add multiply : ℕ) (x : Fp × ℕ)
    (pieces : Fin 8 → List Fp × ℕ) (width : ℕ) (hwidth : ∀ index, (pieces index).1.length ≤ width) :
    (denseCollapsedQuotientCosted read add multiply x pieces).1.length ≤ width := by
  unfold denseCollapsedQuotientCosted
  exact denseWeightedSumCosted_length_le read add multiply x 2048 pieces width hwidth

/-- All eight reads, bounded powers, scalings, and additions are included in the bound. -/
theorem denseCollapsedQuotientCosted_cost_le (read add multiply : ℕ) (x : Fp × ℕ)
    (pieces : Fin 8 → List Fp × ℕ) (width access : ℕ)
    (hwidth : ∀ index, (pieces index).1.length ≤ width) (haccess : ∀ index, (pieces index).2 ≤ access) :
    (denseCollapsedQuotientCosted read add multiply x pieces).2 ≤
      denseWeightedSumCostBudget read add multiply x.2 2048 8 width access := by
  unfold denseCollapsedQuotientCosted
  exact denseWeightedSumCosted_cost_le read add multiply x 2048 pieces width access hwidth haccess

/-- Materialize the actual two-coefficient linear mask and retain both coefficient reads. -/
def denseLinearMaskCosted (constant linear : Fp × ℕ) : List Fp × ℕ :=
  ([constant.1, linear.1], constant.2 + linear.2 + 3)

/-- The stored linear mask is exactly the polynomial used by the optimized prover. -/
theorem denseLinearMaskCosted_result (constant linear : Fp × ℕ) :
    densePolynomial (denseLinearMaskCosted constant linear).1 = linearMaskPolynomial (constant.1, linear.1) := by
  simp only [denseLinearMaskCosted, densePolynomial, linearMaskPolynomial, mul_zero, add_zero]
  rw [mul_comm CompPoly.CPolynomial.X]

/-- The linear mask has its full two-coefficient storage layout, even when a coefficient vanishes. -/
theorem denseLinearMaskCosted_length (constant linear : Fp × ℕ) :
    (denseLinearMaskCosted constant linear).1.length = 2 := rfl

end Zcash.Snark.ZeroKnowledge
