import Zcash.Snark.ZeroKnowledge.PlonkPrefix
import Zcash.Snark.ZeroKnowledge.PlonkProductFactors

/-!
# Fresh-challenge bounds for the computed product denominators

The concrete column prefix is fixed before the product challenges, so the finite
factor bound applies to the denominators actually read by the reference scans.
With fifteen packed permutation references the bound is `42882m/p + 2 × bias`.
An arbitrary random private state is allowed before the two fresh challenges.

This bounds a sufficient exceptional event for the reference construction, without
conditioning on successful sorting. `PlonkConstructedSimulation` includes this term
in the joint row-error bound with the remaining construction prerequisites explicit.
`PlonkProductChallenges` connects these coins to the full independent challenge tape;
the online schedule and Fiat-Shamir still require separate refinement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- Replace only the two product challenges by the newly sampled coins. -/
def withProductChallenges {k : ℕ} (ch : Challenges k Fp) (coins : ProductChallengeTape) :
    Challenges k Fp := { ch with beta := coins 0, gamma := coins 1 }

/-- The actual lookup input factor list is fixed before the product challenges. -/
theorem plonkProductBetaOffsets_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) (tape : Fin (126 * actions) → Fp) :
    plonkProductBetaOffsets (actions := actions) (plonkTotalColumnRows vk pub witness ch tape) =
      plonkProductBetaOffsets (actions := actions) (plonkTotalColumnRows vk pub witness ch' tape) := by
  have hb (a : Fin actions) (l : Fin 3) :=
    plonkTotalColumnRows_polynomial_before_products vk pub witness ch ch' htheta tape
      (.lookupInput a l) (privateColumnIndex_bounds (.lookupInput a l)).2
  simp only [plonkProductBetaOffsets, hb]

/-- Both the packed permutation factors and lookup table factors are fixed before the product coins. -/
theorem plonkProductGammaForms_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch ch' : Challenges k Fp)
    (htheta : ch.theta = ch'.theta) (tape : Fin (126 * actions) → Fp) :
    plonkProductGammaForms pub (plonkTotalColumnRows vk pub witness ch tape) vk.permutationChunks =
      plonkProductGammaForms pub (plonkTotalColumnRows vk pub witness ch' tape) vk.permutationChunks := by
  have ht (a : Fin actions) (l : Fin 3) :=
    plonkTotalColumnRows_polynomial_before_products vk pub witness ch ch' htheta tape
      (.lookupTable a l) (privateColumnIndex_bounds (.lookupTable a l)).2
  have hp (a : Fin actions) :
      plonkPermutationPairPolynomials pub (plonkTotalColumnRows vk pub witness ch tape)
          a vk.permutationChunks.flatten =
        plonkPermutationPairPolynomials pub (plonkTotalColumnRows vk pub witness ch' tape)
          a vk.permutationChunks.flatten := by
    have hcut : 10 * actions ≤ 16 * actions := by omega
    rw [← plonkPermutationPairPolynomials_take _ _ (16 * actions) hcut,
      ← plonkPermutationPairPolynomials_take pub (plonkTotalColumnRows vk pub witness ch' tape)
        (16 * actions) hcut,
      plonkTotalColumnRows_take_challenges vk pub witness ch ch' htheta tape]
  simp only [plonkProductGammaForms, ht, hp]

/-- Fresh wide-reduced product coins bound the actual reference denominators on every fixed row tape. -/
theorem widePlonkProductDenominators_bad_le {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) :
    wideProductChallenges.toOuterMeasure {coins |
      ¬ plonkProductDenominatorsNonzero pub
        (plonkTotalColumnRows vk pub witness (withProductChallenges ch coins) tape)
        vk.permutationChunks (coins 0) (coins 1)} ≤
      ((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        2 * challenge255Bias := by
  let rows := plonkTotalColumnRows vk pub witness ch tape
  have hsubset : {coins | ¬ plonkProductDenominatorsNonzero pub
      (plonkTotalColumnRows vk pub witness (withProductChallenges ch coins) tape)
      vk.permutationChunks (coins 0) (coins 1)} ⊆
      {coins | productDenominatorListBad (plonkProductBetaOffsets (actions := actions) rows)
        (plonkProductGammaForms pub rows vk.permutationChunks) coins} := by
    intro coins hbad
    by_contra hgood
    apply hbad
    apply plonkProductDenominatorsNonzero_of_not_listBad
    rwa [plonkProductBetaOffsets_challenges vk pub witness (withProductChallenges ch coins) ch rfl tape,
      plonkProductGammaForms_challenges vk pub witness (withProductChallenges ch coins) ch rfl tape]
  apply le_trans (MeasureTheory.measure_mono hsubset)
  have h := wideProductDenominatorList_bad_le (plonkProductBetaOffsets (actions := actions) rows)
    (plonkProductGammaForms pub rows vk.permutationChunks)
  rw [plonkProductBetaOffsets_length, plonkProductGammaForms_length] at h
  have hcount : 3 * actions * 2042 + (vk.permutationChunks.flatten.length + 3) * actions * 2042 =
      (vk.permutationChunks.flatten.length + 6) * actions * 2042 := by ring
  simpa only [hcount] using h

/-- Fifteen packed references give the pinned `42882m/p + 2 × bias` denominator bound. -/
theorem widePinnedPlonkProductDenominators_bad_le {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) (hpacked : vk.permutationChunks.flatten.length = 15) :
    wideProductChallenges.toOuterMeasure {coins |
      ¬ plonkProductDenominatorsNonzero pub
        (plonkTotalColumnRows vk pub witness (withProductChallenges ch coins) tape)
        vk.permutationChunks (coins 0) (coins 1)} ≤
      (((42882 * actions : ℕ) : ℝ≥0∞) / scalarFieldOrder) + 2 * challenge255Bias := by
  have hcount : (vk.permutationChunks.flatten.length + 6) * actions * 2042 = 42882 * actions := by
    rw [hpacked]
    omega
  simpa only [hcount] using widePlonkProductDenominators_bad_le vk pub witness ch tape

/-- Any private state law before fresh product challenges preserves the concrete denominator bound. -/
theorem widePlonkProductDenominators_mixture_bad_le {actions k : ℕ} {G A : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (stateLaw : PMF A)
    (ch : A → Challenges k Fp) (tape : A → Fin (126 * actions) → Fp) :
    (stateLaw.bind fun state => wideProductChallenges.map (Prod.mk state)).toOuterMeasure {view |
      ¬ plonkProductDenominatorsNonzero pub
        (plonkTotalColumnRows vk pub witness (withProductChallenges (ch view.1) view.2) (tape view.1))
        vk.permutationChunks (view.2 0) (view.2 1)} ≤
      ((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        2 * challenge255Bias := by
  rw [PMF.toOuterMeasure_bind_apply]
  have hpoint (state : A) :
      (wideProductChallenges.map (Prod.mk state)).toOuterMeasure {view |
        ¬ plonkProductDenominatorsNonzero pub
          (plonkTotalColumnRows vk pub witness (withProductChallenges (ch view.1) view.2) (tape view.1))
          vk.permutationChunks (view.2 0) (view.2 1)} ≤
        ((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          2 * challenge255Bias := by
    rw [PMF.toOuterMeasure_map_apply]
    exact widePlonkProductDenominators_bad_le vk pub witness (ch state) (tape state)
  calc
    _ ≤ ∑' state, stateLaw state *
        (((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          2 * challenge255Bias) :=
      ENNReal.tsum_le_tsum fun state => mul_le_mul_right (hpoint state) (stateLaw state)
    _ = _ := by rw [ENNReal.tsum_mul_right, stateLaw.tsum_coe, one_mul]

/-- Completed partial attempts have the same denominator bound without conditioning on success.

The event is completion *and* a zero product denominator. Failed sorts are not
bounded by this theorem and must still be accounted for in the full prover view. -/
theorem widePlonkColumnAttempt_productDenominators_bad_le {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges k Fp)
    (tape : Fin (126 * actions) → Fp) :
    wideProductChallenges.toOuterMeasure {coins |
      (plonkColumnAttempt vk pub witness (withProductChallenges ch coins) tape).complete = true ∧
      ¬ plonkProductDenominatorsNonzero pub
        (plonkColumnAttempt vk pub witness (withProductChallenges ch coins) tape).columns
        vk.permutationChunks (coins 0) (coins 1)} ≤
      ((((vk.permutationChunks.flatten.length + 6) * actions * 2042 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        2 * challenge255Bias := by
  apply le_trans (MeasureTheory.measure_mono ?_) (widePlonkProductDenominators_bad_le vk pub witness ch tape)
  intro coins hbad
  simpa only [plonkColumnAttempt_eq_totalRows_of_complete vk pub witness
    (withProductChallenges ch coins) tape hbad.1] using hbad.2

end Zcash.Snark.ZeroKnowledge
