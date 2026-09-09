import Zcash.Snark.ZeroKnowledge.DenseOpeningGroupCost
import Zcash.Snark.ZeroKnowledge.DensePolynomialFold

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open CompPoly

/-- Construct and fold one full original opening group using stored polynomial arithmetic. -/
@[irreducible] def denseOpeningPolynomialCosted (equal read add multiply : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (x1 : Fp × ℕ) (group : Fin 5) : List Fp × ℕ :=
  let members := denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group
  let result := densePolynomialFoldCosted read add multiply x1 members.1
  (result.1, members.2 + result.2 + 1)

/-- Every polynomial operation and every group member erases to the same original opening polynomial. -/
theorem denseOpeningPolynomialCosted_result (equal read add multiply : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (x1 : Fp × ℕ) (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp)
    (hinstances : ∀ action, densePolynomial (instances action).1 = pub.instances action)
    (hfixed : ∀ index, densePolynomial (fixed index).1 = pub.fixed index)
    (hsigma : ∀ index, densePolynomial (sigma index).1 = pub.sigma index)
    (hcolumns : ∀ id : PrivateColumnId actions,
      densePolynomial (privateColumnCoefficientsCosted equal read columns id).1 = privateColumnPolynomial rows id)
    (hquotient : densePolynomial quotient.1 = plonkCollapsedQuotient x pieces)
    (hlinear : densePolynomial linear.1 = linearMaskPolynomial coefficients) (group : Fin 5) :
    densePolynomial (denseOpeningPolynomialCosted equal read add multiply instances fixed sigma
      columns quotient linear x1 group).1 = plonkOpeningPolynomials pub rows x x1.1 pieces coefficients group := by
  unfold denseOpeningPolynomialCosted
  change densePolynomial (densePolynomialFoldCosted read add multiply x1
    (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).1).1 = _
  exact (densePolynomialFoldCosted_result read add multiply x1
    (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).1).trans
    (congrArg (plonkPolynomialFold x1.1)
      (denseOpeningGroupMembersCosted_result equal read instances fixed sigma columns quotient linear pub rows x
        pieces coefficients hinstances hfixed hsigma hcolumns hquotient hlinear group))

/-- The folded polynomial fits the common coefficient storage capacity. -/
theorem denseOpeningPolynomialCosted_length_le (equal read add multiply : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (x1 : Fp × ℕ) (width : ℕ)
    (hinstances : ∀ action, (instances action).1.length ≤ width)
    (hfixed : ∀ index, (fixed index).1.length ≤ width) (hsigma : ∀ index, (sigma index).1.length ≤ width)
    (hcolumns : ∀ column ∈ columns, column.length ≤ width)
    (hquotient : quotient.1.length ≤ width) (hlinear : linear.1.length ≤ width) (group : Fin 5) :
    (denseOpeningPolynomialCosted equal read add multiply instances fixed sigma columns quotient linear x1 group).1.length ≤ width := by
  unfold denseOpeningPolynomialCosted
  exact densePolynomialFoldCosted_length_le read add multiply x1
    (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).1 width
    (denseOpeningGroupMembersCosted_width equal read instances fixed sigma columns quotient linear width
      hinstances hfixed hsigma hcolumns hquotient hlinear group)

/-- Complete group construction and polynomial-fold budget. -/
def denseOpeningPolynomialCostBudget (equal read add multiply actions columns access challengeAccess width : ℕ) : ℕ :=
  denseOpeningGroupMembersCostBudget equal read actions columns access +
    (9 * actions + 46) * densePolynomialFoldStepBudget read add multiply challengeAccess width + 2

/-- The complete opening polynomial has a bound derived from every counted member and coefficient. -/
theorem denseOpeningPolynomialCosted_cost_le (equal read add multiply : ℕ) {actions : ℕ}
    (instances : Fin actions → List Fp × ℕ) (fixed : Fin 29 → List Fp × ℕ)
    (sigma : Fin 15 → List Fp × ℕ) (columns : List (List Fp))
    (quotient linear : List Fp × ℕ) (x1 : Fp × ℕ) (width access : ℕ)
    (hinstances : ∀ action, (instances action).1.length ≤ width)
    (hfixed : ∀ index, (fixed index).1.length ≤ width) (hsigma : ∀ index, (sigma index).1.length ≤ width)
    (hcolumns : ∀ column ∈ columns, column.length ≤ width)
    (hquotient : quotient.1.length ≤ width) (hlinear : linear.1.length ≤ width)
    (hiRead : ∀ action, (instances action).2 ≤ access)
    (hfRead : ∀ index, (fixed index).2 ≤ access) (hsRead : ∀ index, (sigma index).2 ≤ access)
    (hqRead : quotient.2 ≤ access) (hlRead : linear.2 ≤ access) (group : Fin 5) :
    (denseOpeningPolynomialCosted equal read add multiply instances fixed sigma columns quotient linear x1 group).2 ≤
      denseOpeningPolynomialCostBudget equal read add multiply actions columns.length access x1.2 width := by
  have hm := denseOpeningGroupMembersCosted_cost_le equal read instances fixed sigma columns quotient linear access
    hiRead hfRead hsRead hqRead hlRead group
  have hl := denseOpeningGroupMembersCosted_length_le equal read instances fixed sigma columns quotient linear group
  have hf := densePolynomialFoldCosted_cost_le read add multiply x1
    (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).1 width
    (denseOpeningGroupMembersCosted_width equal read instances fixed sigma columns quotient linear width
      hinstances hfixed hsigma hcolumns hquotient hlinear group)
  have hh := Nat.mul_le_mul_right (densePolynomialFoldStepBudget read add multiply x1.2 width) hl
  unfold denseOpeningPolynomialCosted
  change (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).2 +
    (densePolynomialFoldCosted read add multiply x1
      (denseOpeningGroupMembersCosted equal read instances fixed sigma columns quotient linear group).1).2 + 1 ≤ _
  unfold denseOpeningPolynomialCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
