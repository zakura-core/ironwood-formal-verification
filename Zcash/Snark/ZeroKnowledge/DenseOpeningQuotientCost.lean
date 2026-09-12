import Zcash.Snark.ZeroKnowledge.DenseLagrangeCost
import Zcash.Snark.ZeroKnowledge.DensePolynomialEvaluation
import Zcash.Snark.ZeroKnowledge.DensePolynomialMultiply
import Zcash.Snark.ZeroKnowledge.DenseVanishingDivision
import Zcash.Snark.ZeroKnowledge.MultiopenPolynomial

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Construct an opening quotient from its stored polynomial and the original ordered point list. -/
@[irreducible] def denseOpeningQuotientCosted (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (poly points : List Fp) : List Fp × ℕ :=
  let values := densePolynomialNodeValuesCosted read costs.add costs.multiply poly points
  let interpolant := denseLagrangeCoefficientsCosted costs read omegaAccess k points values.1
  let residual := denseSubCosted read costs.add costs.negate poly interpolant.1
  let quotient := denseDivVanishingCosted equal read costs.add costs.multiply points residual.1
  (quotient.1, values.2 + interpolant.2 + residual.2 + quotient.2 + 3)

/-- Erasure preserves the actual interpolation, point deduplication, and totalized division independently. -/
theorem denseOpeningQuotientCosted_result (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (hk : k ≤ 32) (poly points : List Fp) (hpoints : points.length ≤ 2 ^ k) :
    densePolynomial (denseOpeningQuotientCosted costs equal read omegaAccess k poly points).1 =
      (PolynomialOpeningGroup.mk (densePolynomial poly) points).quotient := by
  unfold denseOpeningQuotientCosted
  change densePolynomial (denseDivVanishingCosted equal read costs.add costs.multiply points
    (denseSubCosted read costs.add costs.negate poly
      (denseLagrangeCoefficientsCosted costs read omegaAccess k points
        (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1).1).1).1 = _
  rewrite [denseDivVanishingCosted_result, denseSubCosted_result,
    denseLagrangeCoefficientsCosted_result costs read omegaAccess k hk points
      (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1 hpoints,
    densePolynomialNodeValuesCosted_result]
  rfl

/-- The retained quotient storage fits the larger of the original polynomial and interpolation capacity. -/
theorem denseOpeningQuotientCosted_length (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (poly points : List Fp) :
    (denseOpeningQuotientCosted costs equal read omegaAccess k poly points).1.length = max poly.length (2 ^ k) := by
  unfold denseOpeningQuotientCosted
  change (denseDivVanishingCosted equal read costs.add costs.multiply points
    (denseSubCosted read costs.add costs.negate poly
      (denseLagrangeCoefficientsCosted costs read omegaAccess k points
        (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1).1).1).1.length = _
  rewrite [denseDivVanishingCosted_length, denseSubCosted_length, denseLagrangeCoefficientsCosted_length]
  rfl

/-- Full opening-quotient budget in the actual input storage dimensions. -/
def denseOpeningQuotientCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess k width points : ℕ) : ℕ :=
  (points * (width * (2 * read + costs.add + costs.multiply + 2) + 2) + 1) +
    denseLagrangeCoefficientsCostBudget costs read omegaAccess k points points +
    (2 ^ k * (read + costs.negate + 2) + width * (2 * read + costs.add + 2) + 3) +
    (points * points * (equal + 2) + points *
      (max width (2 ^ k) * (read + costs.add + costs.multiply + 5) + read + 9) + 3) + 3

/-- Complete input evaluation, indexed interpolation, subtraction, and quotient construction fit one bound. -/
theorem denseOpeningQuotientCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (poly points : List Fp) :
    (denseOpeningQuotientCosted costs equal read omegaAccess k poly points).2 ≤
      denseOpeningQuotientCostBudget costs equal read omegaAccess k poly.length points.length := by
  have hv := densePolynomialNodeValuesCosted_cost_le read costs.add costs.multiply poly points
  have hi := denseLagrangeCoefficientsCosted_cost_le costs read omegaAccess k points
    (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1
  rewrite [densePolynomialNodeValuesCosted_length] at hi
  have hs := denseSubCosted_cost_le read costs.add costs.negate poly
    (denseLagrangeCoefficientsCosted costs read omegaAccess k points
      (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1).1
  rewrite [denseLagrangeCoefficientsCosted_length] at hs
  have hq := denseDivVanishingCosted_cost_le equal read costs.add costs.multiply points
    (denseSubCosted read costs.add costs.negate poly
      (denseLagrangeCoefficientsCosted costs read omegaAccess k points
        (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1).1).1
  rewrite [denseSubCosted_length, denseLagrangeCoefficientsCosted_length] at hq
  unfold denseOpeningQuotientCosted
  change (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).2 +
    (denseLagrangeCoefficientsCosted costs read omegaAccess k points
      (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1).2 +
    (denseSubCosted read costs.add costs.negate poly
      (denseLagrangeCoefficientsCosted costs read omegaAccess k points
        (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1).1).2 +
    (denseDivVanishingCosted equal read costs.add costs.multiply points
      (denseSubCosted read costs.add costs.negate poly
        (denseLagrangeCoefficientsCosted costs read omegaAccess k points
          (densePolynomialNodeValuesCosted read costs.add costs.multiply poly points).1).1).1).2 + 3 ≤ _
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hv hi) hs) hq) 3

end Zcash.Snark.ZeroKnowledge
