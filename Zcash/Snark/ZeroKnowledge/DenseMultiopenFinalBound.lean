import Zcash.Snark.ZeroKnowledge.DenseMultiopenFinalCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Complete bound for the retained quotient and the final IPA polynomial. -/
def denseMultiopenFinalCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess k x2Read x4Read groups width points : ℕ) : ℕ :=
  denseMultiopenQuotientCostBudget costs equal read omegaAccess k x2Read groups width points +
    groups * (read + 2) + (groups + 1) *
      densePolynomialFoldStepBudget read costs.add costs.multiply x4Read (max width (2 ^ k)) + 5

/-- All quotient construction, stored member reads, and the final polynomial fold fit one derived budget. -/
theorem denseMultiopenFinalCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (x2 x4 : Fp × ℕ) (groups : List StoredOpeningGroup) (width points : ℕ)
    (hwidth : ∀ group ∈ groups, group.coefficients.length ≤ width)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ points) :
    (denseMultiopenFinalCosted costs equal read omegaAccess k x2 x4 groups).2 ≤
      denseMultiopenFinalCostBudget costs equal read omegaAccess k x2.2 x4.2 groups.length width points := by
  let quotient := denseMultiopenQuotientCosted costs equal read omegaAccess k x2 groups
  let polynomials := mapListCosted (fun group => (group.coefficients, read + 1)) groups
  have hq := denseMultiopenQuotientCosted_cost_le costs equal read omegaAccess k x2 groups width points hwidth hpoints
  have hp := mapListCosted_cost_le (fun group : StoredOpeningGroup => (group.coefficients, read + 1)) groups
    (read + 1) (fun _ _ => le_rfl)
  have hlength : polynomials.1.length = groups.length := by
    change (mapListCosted (fun group => (group.coefficients, read + 1)) groups).1.length = _
    rewrite [mapListCosted_result, List.length_map]
    rfl
  have hw : ∀ poly ∈ quotient.1 :: polynomials.1, poly.length ≤ max width (2 ^ k) := by
    intro poly hpoly
    rcases List.mem_cons.mp hpoly with rfl | hpoly
    · exact denseMultiopenQuotientCosted_length_le costs equal read omegaAccess k x2 groups width hwidth
    · change poly ∈ (mapListCosted (fun group => (group.coefficients, read + 1)) groups).1 at hpoly
      simp only [mapListCosted_result, List.mem_map] at hpoly
      obtain ⟨group, hgroup, rfl⟩ := hpoly
      exact (hwidth group hgroup).trans (Nat.le_max_left _ _)
  have hf := densePolynomialFoldCosted_cost_le read costs.add costs.multiply x4
    (quotient.1 :: polynomials.1) (max width (2 ^ k)) hw
  rewrite [List.length_cons, hlength] at hf
  change polynomials.2 ≤ groups.length * (read + 2) + 1 at hp
  change quotient.2 ≤ denseMultiopenQuotientCostBudget costs equal read omegaAccess k x2.2
    groups.length width points at hq
  unfold denseMultiopenFinalCosted
  change quotient.2 + polynomials.2 +
    (densePolynomialFoldCosted read costs.add costs.multiply x4 (quotient.1 :: polynomials.1)).2 + 3 ≤ _
  unfold denseMultiopenFinalCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
