import Zcash.Snark.ZeroKnowledge.MultiopenIpa

/-!
# The quotient fallback at an opening-node collision

Opening `X` at `0` gives quotient `1`. At the later point `0`, the prover
therefore supplies value `1` for the final polynomial `1 + X`, while the
verifier's totalized division gives `0`. This example detects substitution
of the verifier's reconstructed value into the prover's IPA input.
-/

namespace Zcash.Snark.ZeroKnowledge.Zakura

open Zcash.Arithmetic (Fp URS)
open CompPoly

/-- A degree-one polynomial whose quotient has a nonzero value at its only opening node. -/
def linearCollisionGroup : BlindedOpeningGroup :=
  { polynomial := CPolynomial.X, points := [0], blind := 0 }

/-- Dividing the zero-interpolation residual `X` by its vanishing polynomial `X` gives `1`. -/
theorem linearCollisionGroup_quotient : linearCollisionGroup.toPolynomialOpeningGroup.quotient = 1 := by
  have hinterp : linearCollisionGroup.toPolynomialOpeningGroup.interpolant = 0 := by
    apply CPolynomial.toPoly_injective
    simp [PolynomialOpeningGroup.interpolant, toPoly_lagrangePoly,
      linearCollisionGroup, PolynomialOpeningGroup.values, Lagrange.interpolate_apply,
      List.getD]
  apply CPolynomial.toPoly_injective
  rw [PolynomialOpeningGroup.quotient, hinterp, sub_zero, CPolynomial.div_toPoly_eq_div]
  simp [linearCollisionGroup, PolynomialOpeningGroup.vanishing, vanishingProd,
    CPolynomial.toPoly_sub, CPolynomial.C_toPoly, CPolynomial.X_toPoly]

/-- At the colliding point, the prover's IPA value is `1` and the verifier's reconstructed value is `0`. -/
theorem openingNodeCollision_usesPolynomialValue {G : Type*} [AddCommGroup G] [Module Fp G]
    (urs : URS G) (xi z blind : Fp) (rounds : Fin urs.k → Fp) :
    (computedMultiopenIpaPublic urs 1 1 0 xi z blind rounds [linearCollisionGroup]).value = 1 ∧
      (computedMultiopenOpening urs 1 1 0 blind [linearCollisionGroup]).2 = 0 := by
  have hquot : multiopenQuotientPolynomial 1 [linearCollisionGroup.toPolynomialOpeningGroup] = 1 := by
    simpa only [multiopenQuotientPolynomial, List.map_cons, List.map_nil, plonkPolynomialFold,
      List.foldl_cons, List.foldl_nil, zero_mul, zero_add] using linearCollisionGroup_quotient
  constructor
  · change (multiopenFinalPolynomial 1 1 [linearCollisionGroup]).eval 0 = 1
    simp [multiopenFinalPolynomial, hquot, plonkPolynomialFold, linearCollisionGroup]
  · simp [computedMultiopenOpening, multiopenCombine_eq_pair, linearCollisionGroup,
      PolynomialOpeningGroup.forVerifier, PolynomialOpeningGroup.values, multiopenEval, lagrangeEval]

end Zcash.Snark.ZeroKnowledge.Zakura
