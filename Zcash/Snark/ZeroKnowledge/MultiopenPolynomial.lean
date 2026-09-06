import Zcash.Snark.ZeroKnowledge.PolynomialCommitment
import Zcash.Snark.Soundness.Multiopen.ValueCheck

/-!
# The honest multi-opening quotient and the verifier's inferred value

Each group uses the existing `lagrangePoly` interpolant of its actual polynomial values.
Subtracting that interpolant makes the numerator divisible by the group's vanishing
polynomial. The computed quotient therefore evaluates to precisely the rational expression
in `multiopenEval`, whenever the later point avoids the group's nodes.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open CompPoly

/-- One already-collapsed opening polynomial and its ordered, distinct opening points. -/
structure PolynomialOpeningGroup where
  polynomial : CPoly
  points : List Fp

/-- The claimed evaluations in the honest execution are evaluations of the actual polynomial. -/
def PolynomialOpeningGroup.values (group : PolynomialOpeningGroup) : List Fp :=
  group.points.map fun point => group.polynomial.eval point

/-- Reuse the verifier development's coefficient-form interpolant. -/
def PolynomialOpeningGroup.interpolant (group : PolynomialOpeningGroup) : CPoly :=
  lagrangePoly group.points group.values

/-- The group's vanishing polynomial, with each opening point occurring once. -/
def PolynomialOpeningGroup.vanishing (group : PolynomialOpeningGroup) : CPoly :=
  vanishingProd group.points.toFinset

/-- The coefficient polynomial sent into the `x₂` fold. -/
def PolynomialOpeningGroup.quotient (group : PolynomialOpeningGroup) : CPoly :=
  (group.polynomial - group.interpolant).div group.vanishing

/-- An honest group's interpolation residual vanishes at every opened point. -/
theorem PolynomialOpeningGroup.residual_eval (group : PolynomialOpeningGroup)
    (hnodes : group.points.Nodup) (point : Fp) (hpoint : point ∈ group.points) :
    (group.polynomial - group.interpolant).eval point = 0 := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hpoint
  have hnode := lagrangePoly_eval_node (evals := group.values)
    (List.nodup_iff_injective_get.mp hnodes) i
  rw [PolynomialOpeningGroup.values,
    List.getD_eq_getElem _ _ (by simp), List.getElem_map] at hnode
  have heval : group.interpolant.eval point = group.polynomial.eval point := by
    simpa only [PolynomialOpeningGroup.interpolant, PolynomialOpeningGroup.values, ← hi] using hnode
  rw [CPolynomial.eval_sub, heval, sub_self]

/-- The vanishing polynomial is monic, including the empty-point case. -/
theorem PolynomialOpeningGroup.vanishing_monic (group : PolynomialOpeningGroup) :
    group.vanishing.toPoly.Monic := by
  simp only [PolynomialOpeningGroup.vanishing, vanishingProd, CPolynomial.toPoly_prod,
    CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  exact Polynomial.monic_prod_X_sub_C id _

/-- Distinct opened roots imply exact divisibility of the computed interpolation residual. -/
theorem PolynomialOpeningGroup.vanishing_dvd (group : PolynomialOpeningGroup)
    (hnodes : group.points.Nodup) :
    group.vanishing.toPoly ∣ (group.polynomial - group.interpolant).toPoly := by
  simp only [PolynomialOpeningGroup.vanishing, vanishingProd, CPolynomial.toPoly_prod,
    CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  apply Finset.prod_dvd_of_coprime
  · intro a _ b _ hab
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab
  · intro point hpoint
    apply Polynomial.dvd_iff_isRoot.mpr
    simpa [Polynomial.IsRoot, ← CPolynomial.eval_toPoly, CPolynomial.eval_sub] using
      group.residual_eval hnodes point (List.mem_toFinset.mp hpoint)

/-- The actual division result satisfies the polynomial identity needed for the opening. -/
theorem PolynomialOpeningGroup.quotient_identity (group : PolynomialOpeningGroup)
    (hnodes : group.points.Nodup) :
    group.vanishing * group.quotient = group.polynomial - group.interpolant := by
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.toPoly_mul, PolynomialOpeningGroup.quotient, CPolynomial.div_toPoly_eq_div]
  exact EuclideanDomain.mul_div_cancel' group.vanishing_monic.ne_zero (group.vanishing_dvd hnodes)

/-- The verifier's repeated inversions divide by the whole node product. -/
theorem opening_denominator_fold (points : List Fp) (q value : Fp) :
    points.foldl (fun acc point => acc * (q - point)⁻¹) value =
      value / (points.map fun point => q - point).prod := by
  induction points generalizing value with
  | nil => simp
  | cons point points ih =>
    simp [ih, div_eq_mul_inv, mul_assoc, mul_comm]

/-- The computed quotient's evaluation is precisely the verifier's per-group contribution. -/
theorem PolynomialOpeningGroup.quotient_eval (group : PolynomialOpeningGroup)
    (hnodes : group.points.Nodup) (q : Fp) (hq : q ∉ group.points) :
    group.quotient.eval q =
      group.points.foldl (fun acc point => acc * (q - point)⁻¹)
        (group.polynomial.eval q - lagrangeEval q group.points group.values) := by
  have hvanish : group.vanishing.eval q ≠ 0 :=
    vanishingProd_eval_ne (by simpa using hq)
  have hidentity := congrArg (fun poly : CPoly => poly.eval q) (group.quotient_identity hnodes)
  dsimp only at hidentity
  rw [CPolynomial.eval_mul, CPolynomial.eval_sub] at hidentity
  have hinterp : group.interpolant.eval q = lagrangeEval q group.points group.values :=
    lagrangePoly_eval (List.nodup_iff_injective_get.mp hnodes) q
  rw [hinterp] at hidentity
  have heval : group.quotient.eval q =
      (group.polynomial.eval q - lagrangeEval q group.points group.values) / group.vanishing.eval q := by
    apply (eq_div_iff hvanish).mpr
    simpa only [mul_comm] using hidentity
  rw [heval, opening_denominator_fold, PolynomialOpeningGroup.vanishing, vanishingProd_eval,
    List.prod_toFinset _ hnodes]

/-- The public value data supplied to the existing `multiopenEval` routine. -/
def PolynomialOpeningGroup.forVerifier (q : Fp) (group : PolynomialOpeningGroup) :
    List Fp × List Fp × Fp :=
  (group.points, group.values, group.polynomial.eval q)

/-- Construct the prover's `Q'` by folding all computed quotient polynomials with `x₂`. -/
def multiopenQuotientPolynomial (x2 : Fp) (groups : List PolynomialOpeningGroup) : CPoly :=
  plonkPolynomialFold x2 (groups.map PolynomialOpeningGroup.quotient)

/-- The whole computed `Q'` evaluates to the value reconstructed by the existing verifier. -/
theorem multiopenQuotientPolynomial_eval (x2 q : Fp) (groups : List PolynomialOpeningGroup)
    (hnodes : ∀ group ∈ groups, group.points.Nodup)
    (hq : ∀ group ∈ groups, q ∉ group.points) :
    (multiopenQuotientPolynomial x2 groups).eval q =
      multiopenEval x2 q (groups.map (PolynomialOpeningGroup.forVerifier q)) := by
  rw [multiopenQuotientPolynomial, plonkPolynomialFold_eval]
  simp only [plonkScalarFold, multiopenEval, List.foldl_map, List.map_map, Function.comp_def]
  apply List.foldl_ext
  intro acc group hgroup
  rw [group.quotient_eval (hnodes group hgroup) q (hq group hgroup)]
  rfl

/-- A group's quotient fits the IPA vector when both the polynomial and node count do. -/
theorem PolynomialOpeningGroup.quotient_natDegree_lt {n : ℕ} (group : PolynomialOpeningGroup)
    (hnodes : group.points.Nodup) (hpos : 0 < group.points.length) (hlen : group.points.length ≤ n)
    (hdegree : group.polynomial.natDegree < n) : group.quotient.natDegree < n := by
  have hinterp : group.interpolant.natDegree < n :=
    lt_of_lt_of_le (lagrangePoly_natDegree_lt (evals := group.values) hpos
      (List.nodup_iff_injective_get.mp hnodes)) hlen
  have hnum : (group.polynomial - group.interpolant).toPoly.natDegree < n := by
    rw [CPolynomial.toPoly_sub]
    apply lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
    simpa only [← CPolynomial.natDegree_toPoly] using max_lt hdegree hinterp
  rw [PolynomialOpeningGroup.quotient, CPolynomial.natDegree_toPoly, CPolynomial.div_toPoly_eq_div]
  exact lt_of_le_of_lt (Polynomial.natDegree_le_natDegree (Polynomial.degree_div_le _ _)) hnum

/-- The folded `Q'` retains the common strict degree bound. -/
theorem multiopenQuotientPolynomial_natDegree_lt {n : ℕ} (hn : 0 < n) (x2 : Fp)
    (groups : List PolynomialOpeningGroup)
    (hnodes : ∀ group ∈ groups, group.points.Nodup)
    (hpos : ∀ group ∈ groups, 0 < group.points.length)
    (hlen : ∀ group ∈ groups, group.points.length ≤ n)
    (hdegree : ∀ group ∈ groups, group.polynomial.natDegree < n) :
    (multiopenQuotientPolynomial x2 groups).natDegree < n := by
  apply plonkPolynomialFold_natDegree_lt hn
  intro poly hpoly
  obtain ⟨group, hgroup, rfl⟩ := List.mem_map.mp hpoly
  exact group.quotient_natDegree_lt (hnodes group hgroup) (hpos group hgroup)
    (hlen group hgroup) (hdegree group hgroup)

end Zcash.Snark.ZeroKnowledge
