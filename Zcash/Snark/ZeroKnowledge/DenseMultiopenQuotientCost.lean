import Zcash.Snark.ZeroKnowledge.DenseOpeningQuotientBounds
import Zcash.Snark.ZeroKnowledge.DensePolynomialFold
import Zcash.Snark.ZeroKnowledge.StoredOpeningGroup

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Read one stored opening group and construct its complete quotient. -/
def storedOpeningQuotientCosted (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (group : StoredOpeningGroup) : List Fp × ℕ :=
  let result := denseOpeningQuotientCosted costs equal read omegaAccess k group.coefficients group.points
  (result.1, result.2 + 2 * read + 1)

/-- The counted stored-group quotient is precisely the original quotient polynomial. -/
theorem storedOpeningQuotientCosted_result (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (hk : k ≤ 32) (group : StoredOpeningGroup) (hpoints : group.points.length ≤ 2 ^ k) :
    densePolynomial (storedOpeningQuotientCosted costs equal read omegaAccess k group).1 =
      group.erase.toPolynomialOpeningGroup.quotient :=
  denseOpeningQuotientCosted_result costs equal read omegaAccess k hk group.coefficients group.points hpoints

/-- Construct every original group quotient and fold them with the source's `x₂` challenge. -/
@[irreducible] def denseMultiopenQuotientCosted (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (x2 : Fp × ℕ) (groups : List StoredOpeningGroup) : List Fp × ℕ :=
  let quotients := mapListCosted (storedOpeningQuotientCosted costs equal read omegaAccess k) groups
  let result := densePolynomialFoldCosted read costs.add costs.multiply x2 quotients.1
  (result.1, quotients.2 + result.2 + 1)

/-- The complete stored `Q'` is the original multi-opening quotient, including exceptional node configurations. -/
theorem denseMultiopenQuotientCosted_result (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (hk : k ≤ 32) (x2 : Fp × ℕ) (groups : List StoredOpeningGroup)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 2 ^ k) :
    densePolynomial (denseMultiopenQuotientCosted costs equal read omegaAccess k x2 groups).1 =
      multiopenQuotientPolynomial x2.1 (groups.map fun group => group.erase.toPolynomialOpeningGroup) := by
  unfold denseMultiopenQuotientCosted
  change densePolynomial (densePolynomialFoldCosted read costs.add costs.multiply x2
    (mapListCosted (storedOpeningQuotientCosted costs equal read omegaAccess k) groups).1).1 = _
  rewrite [densePolynomialFoldCosted_result, mapListCosted_result, List.map_map]
  unfold multiopenQuotientPolynomial
  rewrite [List.map_map]
  apply congrArg (plonkPolynomialFold x2.1)
  apply List.map_congr_left
  intro group hgroup
  exact storedOpeningQuotientCosted_result costs equal read omegaAccess k hk group (hpoints group hgroup)

/-- Quotient preparation retains at most the common polynomial or interpolation width. -/
theorem denseMultiopenQuotientCosted_length_le (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (x2 : Fp × ℕ) (groups : List StoredOpeningGroup) (width : ℕ)
    (hwidth : ∀ group ∈ groups, group.coefficients.length ≤ width) :
    (denseMultiopenQuotientCosted costs equal read omegaAccess k x2 groups).1.length ≤ max width (2 ^ k) := by
  unfold denseMultiopenQuotientCosted
  apply densePolynomialFoldCosted_length_le
  intro poly hpoly
  simp only [mapListCosted_result, List.mem_map] at hpoly
  obtain ⟨group, hgroup, rfl⟩ := hpoly
  change (denseOpeningQuotientCosted costs equal read omegaAccess k group.coefficients group.points).1.length ≤ _
  rewrite [denseOpeningQuotientCosted_length]
  exact max_le_max (hwidth group hgroup) le_rfl

/-- Complete budget for constructing and folding all opening quotients. -/
def denseMultiopenQuotientCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess k challengeAccess groups width points : ℕ) : ℕ :=
  groups * (denseOpeningQuotientCostBudget costs equal read omegaAccess k width points + 2 * read + 2) +
    groups * densePolynomialFoldStepBudget read costs.add costs.multiply challengeAccess (max width (2 ^ k)) + 3

/-- The complete `Q'` counter is bounded from the actual stored group dimensions and primitive prices. -/
theorem denseMultiopenQuotientCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (x2 : Fp × ℕ) (groups : List StoredOpeningGroup) (width points : ℕ)
    (hwidth : ∀ group ∈ groups, group.coefficients.length ≤ width)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ points) :
    (denseMultiopenQuotientCosted costs equal read omegaAccess k x2 groups).2 ≤
      denseMultiopenQuotientCostBudget costs equal read omegaAccess k x2.2 groups.length width points := by
  let quotients := mapListCosted (storedOpeningQuotientCosted costs equal read omegaAccess k) groups
  have hq := mapListCosted_cost_le (storedOpeningQuotientCosted costs equal read omegaAccess k) groups
    (denseOpeningQuotientCostBudget costs equal read omegaAccess k width points + 2 * read + 1) (by
      intro group hgroup
      have h := (denseOpeningQuotientCosted_cost_le costs equal read omegaAccess k group.coefficients group.points).trans
        (denseOpeningQuotientCostBudget_mono_lengths costs equal read omegaAccess k
          (hwidth group hgroup) (hpoints group hgroup))
      exact Nat.add_le_add_right (Nat.add_le_add_right h (2 * read)) 1)
  have hlength : quotients.1.length = groups.length := by
    change (mapListCosted (storedOpeningQuotientCosted costs equal read omegaAccess k) groups).1.length = _
    rewrite [mapListCosted_result, List.length_map]
    rfl
  have hw : ∀ poly ∈ quotients.1, poly.length ≤ max width (2 ^ k) := by
    intro poly hpoly
    change poly ∈ (mapListCosted (storedOpeningQuotientCosted costs equal read omegaAccess k) groups).1 at hpoly
    simp only [mapListCosted_result, List.mem_map] at hpoly
    obtain ⟨group, hgroup, rfl⟩ := hpoly
    change (denseOpeningQuotientCosted costs equal read omegaAccess k group.coefficients group.points).1.length ≤ _
    rewrite [denseOpeningQuotientCosted_length]
    exact max_le_max (hwidth group hgroup) le_rfl
  have hf := densePolynomialFoldCosted_cost_le read costs.add costs.multiply x2 quotients.1 (max width (2 ^ k)) hw
  rewrite [hlength] at hf
  unfold denseMultiopenQuotientCosted
  change quotients.2 + (densePolynomialFoldCosted read costs.add costs.multiply x2 quotients.1).2 + 1 ≤ _
  change quotients.2 ≤ groups.length *
    (denseOpeningQuotientCostBudget costs equal read omegaAccess k width points + 2 * read + 2) + 1 at hq
  unfold denseMultiopenQuotientCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
