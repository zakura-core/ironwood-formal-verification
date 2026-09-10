import Zcash.Snark.ZeroKnowledge.DenseMultiopenFinalBound
import Zcash.Snark.ZeroKnowledge.DensePolynomialEvaluation
import Zcash.Snark.ZeroKnowledge.StoredMultiopenBlindCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Stored multi-opening data: quotient-prime coefficients, IPA coefficients, inherited blind, and claimed value. -/
structure StoredMultiopenData where
  quotientPrime : List Fp
  coefficients : List Fp
  blind : Fp
  value : Fp

/-- Compute the prover's multi-opening inputs, evaluating the final polynomial at every challenge. -/
@[irreducible] def storedMultiopenDataCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup) : StoredMultiopenData × ℕ :=
  let final := denseMultiopenFinalCosted costs equal read omegaAccess 2 x2 x4 groups
  let blind := storedMultiopenBlindCosted costs read x4 quotientBlind groups
  let value := listHornerCosted read costs.add costs.multiply point final.1.2
  ({ quotientPrime := final.1.1, coefficients := final.1.2, blind := blind.1, value := value.1 },
    final.2 + blind.2 + value.2 + 1)

/-- The stored quotient-prime has the exact polynomial committed by the original prover. -/
theorem storedMultiopenDataCosted_quotient_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 4) :
    densePolynomial (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 point quotientBlind groups).1.quotientPrime =
      multiopenQuotientPolynomial x2.1 (groups.map fun group => group.erase.toPolynomialOpeningGroup) := by
  unfold storedMultiopenDataCosted
  exact denseMultiopenFinalCosted_quotient_result costs equal read omegaAccess 2 (by decide) x2 x4 groups hpoints

/-- The stored IPA coefficients denote the actual final polynomial, including exceptional input cases. -/
theorem storedMultiopenDataCosted_polynomial_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 4) :
    densePolynomial (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 point quotientBlind groups).1.coefficients =
      multiopenFinalPolynomial x2.1 x4.1 (groups.map StoredOpeningGroup.erase) := by
  unfold storedMultiopenDataCosted
  exact denseMultiopenFinalCosted_result costs equal read omegaAccess 2 (by decide) x2 x4 groups hpoints

/-- The inherited blind remains the original fold of all group blinds and quotient-prime blinding. -/
theorem storedMultiopenDataCosted_blind_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup) :
    (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 point quotientBlind groups).1.blind =
      multiopenFinalBlind x4.1 quotientBlind.1 (groups.map StoredOpeningGroup.erase) := by
  unfold storedMultiopenDataCosted
  exact storedMultiopenBlindCosted_result costs read x4 quotientBlind groups

/-- The supplied IPA value is the final polynomial's evaluation, including opening-node collisions. -/
theorem storedMultiopenDataCosted_value_result (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 4) :
    (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 point quotientBlind groups).1.value =
      (multiopenFinalPolynomial x2.1 x4.1 (groups.map StoredOpeningGroup.erase)).eval point.1 := by
  unfold storedMultiopenDataCosted
  dsimp only
  rewrite [listHornerCosted_densePolynomial_result,
    denseMultiopenFinalCosted_result costs equal read omegaAccess 2 (by decide) x2 x4 groups hpoints]
  rfl

end Zcash.Snark.ZeroKnowledge
