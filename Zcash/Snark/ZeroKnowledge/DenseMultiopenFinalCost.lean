import Zcash.Snark.ZeroKnowledge.DenseMultiopenQuotientCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Construct `Q'` once and retain it while folding the actual final IPA polynomial. -/
@[irreducible] def denseMultiopenFinalCosted (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (x2 x4 : Fp × ℕ) (groups : List StoredOpeningGroup) : (List Fp × List Fp) × ℕ :=
  let quotient := denseMultiopenQuotientCosted costs equal read omegaAccess k x2 groups
  let polynomials := mapListCosted (fun group => (group.coefficients, read + 1)) groups
  let final := densePolynomialFoldCosted read costs.add costs.multiply x4 (quotient.1 :: polynomials.1)
  ((quotient.1, final.1), quotient.2 + polynomials.2 + final.2 + 3)

/-- The retained quotient is precisely the one committed by the original multi-opening prover. -/
theorem denseMultiopenFinalCosted_quotient_result (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (hk : k ≤ 32) (x2 x4 : Fp × ℕ) (groups : List StoredOpeningGroup)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 2 ^ k) :
    densePolynomial (denseMultiopenFinalCosted costs equal read omegaAccess k x2 x4 groups).1.1 =
      multiopenQuotientPolynomial x2.1 (groups.map fun group => group.erase.toPolynomialOpeningGroup) := by
  unfold denseMultiopenFinalCosted
  exact denseMultiopenQuotientCosted_result costs equal read omegaAccess k hk x2 groups hpoints

/-- The complete final coefficient vector denotes the original IPA polynomial, including all exceptional inputs. -/
theorem denseMultiopenFinalCosted_result (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (hk : k ≤ 32) (x2 x4 : Fp × ℕ) (groups : List StoredOpeningGroup)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 2 ^ k) :
    densePolynomial (denseMultiopenFinalCosted costs equal read omegaAccess k x2 x4 groups).1.2 =
      multiopenFinalPolynomial x2.1 x4.1 (groups.map StoredOpeningGroup.erase) := by
  unfold denseMultiopenFinalCosted
  change densePolynomial (densePolynomialFoldCosted read costs.add costs.multiply x4
    ((denseMultiopenQuotientCosted costs equal read omegaAccess k x2 groups).1 ::
      (mapListCosted (fun group => (group.coefficients, read + 1)) groups).1)).1 = _
  rewrite [densePolynomialFoldCosted_result, List.map_cons, mapListCosted_result, List.map_map,
    denseMultiopenQuotientCosted_result costs equal read omegaAccess k hk x2 groups hpoints]
  simp only [multiopenFinalPolynomial, List.map_map, Function.comp_def, StoredOpeningGroup.erase]

/-- The retained `Q'` fits the common polynomial and interpolation capacity. -/
theorem denseMultiopenFinalCosted_quotient_length_le (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (x2 x4 : Fp × ℕ) (groups : List StoredOpeningGroup) (width : ℕ)
    (hwidth : ∀ group ∈ groups, group.coefficients.length ≤ width) :
    (denseMultiopenFinalCosted costs equal read omegaAccess k x2 x4 groups).1.1.length ≤ max width (2 ^ k) := by
  unfold denseMultiopenFinalCosted
  exact denseMultiopenQuotientCosted_length_le costs equal read omegaAccess k x2 groups width hwidth

/-- The final fold preserves the common polynomial and interpolation storage capacity. -/
theorem denseMultiopenFinalCosted_length_le (costs : FieldOperationCosts) (equal read omegaAccess k : ℕ)
    (x2 x4 : Fp × ℕ) (groups : List StoredOpeningGroup) (width : ℕ)
    (hwidth : ∀ group ∈ groups, group.coefficients.length ≤ width) :
    (denseMultiopenFinalCosted costs equal read omegaAccess k x2 x4 groups).1.2.length ≤ max width (2 ^ k) := by
  unfold denseMultiopenFinalCosted
  apply densePolynomialFoldCosted_length_le
  intro poly hpoly
  rcases List.mem_cons.mp hpoly with rfl | hpoly
  · exact denseMultiopenQuotientCosted_length_le costs equal read omegaAccess k x2 groups width hwidth
  · simp only [mapListCosted_result, List.mem_map] at hpoly
    obtain ⟨group, hgroup, rfl⟩ := hpoly
    exact (hwidth group hgroup).trans (Nat.le_max_left _ _)

end Zcash.Snark.ZeroKnowledge
