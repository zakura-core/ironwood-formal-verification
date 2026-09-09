import Zcash.Snark.ZeroKnowledge.DenseMultiopenFinalBound
import Zcash.Snark.ZeroKnowledge.StoredMultiopenValueBound
import Zcash.Snark.ZeroKnowledge.StoredMultiopenBlindCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp URS)

/-- Stored multi-opening data: quotient-prime coefficients, IPA coefficients, inherited blind, and claimed value. -/
structure StoredMultiopenData where
  quotientPrime : List Fp
  coefficients : List Fp
  blind : Fp
  value : Fp

/-- Compute the complete original multi-opening inputs without replacing the verifier's claimed value. -/
@[irreducible] def storedMultiopenDataCosted (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup) : StoredMultiopenData × ℕ :=
  let final := denseMultiopenFinalCosted costs equal read omegaAccess 2 x2 x4 groups
  let blind := storedMultiopenBlindCosted costs read x4 quotientBlind groups
  let value := storedMultiopenValueCosted costs read x2 x4 point groups
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

/-- The supplied IPA value is exactly the original verifier calculation for every challenge. -/
theorem storedMultiopenDataCosted_value_result {G : Type*} [AddCommGroup G] [Module Fp G]
    (costs : FieldOperationCosts) (equal read omegaAccess : ℕ) (urs : URS G)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup) :
    (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 point quotientBlind groups).1.value =
      (computedMultiopenOpening urs x2.1 x4.1 point.1 quotientBlind.1 (groups.map StoredOpeningGroup.erase)).2 := by
  unfold storedMultiopenDataCosted
  exact storedMultiopenValueCosted_computed costs read urs x2 x4 point quotientBlind.1 groups

end Zcash.Snark.ZeroKnowledge
