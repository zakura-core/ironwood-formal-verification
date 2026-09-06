import Zcash.Snark.ZeroKnowledge.MultiopenPolynomial
import Zcash.Snark.ZeroKnowledge.IpaSampling
import Zcash.Snark.ZeroKnowledge.IpaVerifier

/-!
# The computed multi-opening supplies a valid IPA input

The final polynomial and incoming blind are computed by the specified `x₄` folds. The
public commitment and value are computed by the existing verifier's `multiopenCombine`
and `multiopenEval`. Their correspondence is proved, so the IPA simulation theorem's
valid-opening premises are derived for this construction.

The group claims here are actual polynomial evaluations. Connecting the PLONK verifier's
inferred `H_x(x)` to those values still requires the quotient/constraint identity; routing
all groups from the complete proof string is a further integration step.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp Msm URS)
open CompPoly
open Zcash.Common
open scoped ENNReal

/-- A collapsed opening group carries the blind obtained by folding its member blinds. -/
structure BlindedOpeningGroup extends PolynomialOpeningGroup where
  blind : Fp

/-- The polynomial passed to the IPA, with `Q'` first in the final fold. -/
def multiopenFinalPolynomial (x2 x4 : Fp) (groups : List BlindedOpeningGroup) : CPoly :=
  plonkPolynomialFold x4
    (multiopenQuotientPolynomial x2 (groups.map BlindedOpeningGroup.toPolynomialOpeningGroup) ::
      groups.map (fun group => group.polynomial))

/-- Every inherited group blind and the new `Q'` blind enters the identical `x₄` fold. -/
def multiopenFinalBlind (x4 qPrimeBlind : Fp) (groups : List BlindedOpeningGroup) : Fp :=
  plonkScalarFold x4 (qPrimeBlind :: groups.map BlindedOpeningGroup.blind)

section PublicOpening

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Represent a group's public commitment as one term in the existing verifier MSM. -/
def multiopenGroupMsm (urs : URS G) (group : BlindedOpeningGroup) : Msm urs.k Fp G :=
  (Msm.zero urs.k Fp G).appendTerm 1
    (polynomialCommitment urs.g urs.w group.polynomial group.blind)

/-- Compute the public IPA opening with the existing multi-opening verifier operations. -/
def computedMultiopenOpening (urs : URS G) (x2 x4 q qPrimeBlind : Fp)
    (groups : List BlindedOpeningGroup) : Msm urs.k Fp G × Fp :=
  let quotient := multiopenQuotientPolynomial x2 (groups.map BlindedOpeningGroup.toPolynomialOpeningGroup)
  multiopenCombine x4 (polynomialCommitment urs.g urs.w quotient qPrimeBlind)
    (groups.map (multiopenGroupMsm urs)) (groups.map fun group => group.polynomial.eval q)
    (multiopenEval x2 q (groups.map fun group => group.toPolynomialOpeningGroup.forVerifier q))
    (Msm.zero urs.k Fp G)

/-- No group or value is lost when the verifier zips the two lists constructed from the groups. -/
private theorem computedMultiopen_zip (urs : URS G) (q : Fp) (groups : List BlindedOpeningGroup) :
    (groups.map (multiopenGroupMsm urs)).zip (groups.map fun group => group.polynomial.eval q) =
      groups.map fun group => (multiopenGroupMsm urs group, group.polynomial.eval q) := by
  induction groups with
  | nil => rfl
  | cons group groups ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- The public commitment equals the coefficient commitment with the actually folded blind. -/
theorem computedMultiopenOpening_commitment (urs : URS G) (x2 x4 q qPrimeBlind : Fp)
    (groups : List BlindedOpeningGroup) :
    (computedMultiopenOpening urs x2 x4 q qPrimeBlind groups).1.eval urs =
      polynomialCommitment urs.g urs.w (multiopenFinalPolynomial x2 x4 groups)
        (multiopenFinalBlind x4 qPrimeBlind groups) := by
  rw [computedMultiopenOpening, multiopenCombine_eq_pair]
  dsimp only
  rw [Msm.eval_foldl_scale_add, computedMultiopen_zip, Msm.eval_appendTerm, Msm.eval_zero]
  simp only [zero_add, one_smul, List.foldl_map, multiopenGroupMsm, Msm.eval_appendTerm, Msm.eval_zero]
  have h := polynomialCommitment_fold urs.g urs.w x4
    ((multiopenQuotientPolynomial x2 (groups.map BlindedOpeningGroup.toPolynomialOpeningGroup), qPrimeBlind) ::
      groups.map fun group => (group.polynomial, group.blind))
  simpa only [multiopenFinalPolynomial, multiopenFinalBlind, List.map_cons, List.map_map,
    Function.comp_def, commitmentHornerFold, List.foldl_cons, smul_zero, zero_add, List.foldl_map] using h.symm

/-- The verifier's reconstructed scalar is the evaluation of the actual final polynomial. -/
theorem computedMultiopenOpening_value (urs : URS G) (x2 x4 q qPrimeBlind : Fp)
    (groups : List BlindedOpeningGroup) (hnodes : ∀ group ∈ groups, group.points.Nodup)
    (hq : ∀ group ∈ groups, q ∉ group.points) :
    (computedMultiopenOpening urs x2 x4 q qPrimeBlind groups).2 =
      (multiopenFinalPolynomial x2 x4 groups).eval q := by
  have hquot := multiopenQuotientPolynomial_eval x2 q
    (groups.map BlindedOpeningGroup.toPolynomialOpeningGroup)
    (by intro group hgroup; obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgroup; exact hnodes g hg)
    (by intro group hgroup; obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgroup; exact hq g hg)
  rw [computedMultiopenOpening, multiopenCombine_eq_pair]
  dsimp only
  rw [computedMultiopen_zip]
  simp only [multiopenFinalPolynomial, plonkPolynomialFold_eval, plonkScalarFold,
    List.map_cons, List.map_map, Function.comp_def, List.foldl_cons, zero_mul, zero_add,
    List.foldl_map] at hquot ⊢
  rw [hquot]

/-- Public IPA data from the computed verifier opening. -/
def computedMultiopenIpaPublic (urs : URS G) (x2 x4 q xi z qPrimeBlind : Fp)
    (rounds : Fin urs.k → Fp) (groups : List BlindedOpeningGroup) : IpaPublic urs.k Fp G :=
  let opened := computedMultiopenOpening urs x2 x4 q qPrimeBlind groups
  IpaPublic.ofMsm urs opened.1 q opened.2 xi z rounds

end PublicOpening

/-- The final polynomial fits the IPA vector; the coefficient commitment does not truncate it. -/
theorem multiopenFinalPolynomial_natDegree_lt {n : ℕ} (hn : 0 < n) (x2 x4 : Fp)
    (groups : List BlindedOpeningGroup)
    (hnodes : ∀ group ∈ groups, group.points.Nodup)
    (hpos : ∀ group ∈ groups, 0 < group.points.length)
    (hlen : ∀ group ∈ groups, group.points.length ≤ n)
    (hdegree : ∀ group ∈ groups, group.polynomial.natDegree < n) :
    (multiopenFinalPolynomial x2 x4 groups).natDegree < n := by
  apply plonkPolynomialFold_natDegree_lt hn
  intro poly hpoly
  rcases List.mem_cons.mp hpoly with hquot | hgroup
  · subst poly
    apply multiopenQuotientPolynomial_natDegree_lt hn
    all_goals
      intro group hgroup
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgroup
    · exact hnodes g hg
    · exact hpos g hg
    · exact hlen g hg
    · exact hdegree g hg
  · obtain ⟨group, hg, rfl⟩ := List.mem_map.mp hgroup
    exact hdegree group hg

section ValidOpening

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Both IPA opening premises follow from the computed polynomial, blind, and verifier value. -/
theorem computedMultiopenIpaPublic_validOpening (urs : URS G) (x2 x4 q xi z qPrimeBlind : Fp)
    (rounds : Fin urs.k → Fp) (groups : List BlindedOpeningGroup)
    (hnodes : ∀ group ∈ groups, group.points.Nodup)
    (hq : ∀ group ∈ groups, q ∉ group.points)
    (hpos : ∀ group ∈ groups, 0 < group.points.length)
    (hlen : ∀ group ∈ groups, group.points.length ≤ 2 ^ urs.k)
    (hdegree : ∀ group ∈ groups, group.polynomial.natDegree < 2 ^ urs.k) :
    let pub := computedMultiopenIpaPublic urs x2 x4 q xi z qPrimeBlind rounds groups
    let coefficients := polynomialCoefficients (2 ^ urs.k) (multiopenFinalPolynomial x2 x4 groups)
    pub.commitment = commitGen pub.generators coefficients +
        multiopenFinalBlind x4 qPrimeBlind groups • pub.W ∧
      coefficientEvaluation urs.k pub.point coefficients = pub.value := by
  dsimp only [computedMultiopenIpaPublic, IpaPublic.ofMsm]
  constructor
  · exact computedMultiopenOpening_commitment urs x2 x4 q qPrimeBlind groups
  · rw [coefficientEvaluation_polynomialCoefficients _ _
      (multiopenFinalPolynomial_natDegree_lt (by positivity) x2 x4 groups hnodes hpos hlen hdegree)]
    exact (computedMultiopenOpening_value urs x2 x4 q qPrimeBlind groups hnodes hq).symm

end ValidOpening

end Zcash.Snark.ZeroKnowledge
