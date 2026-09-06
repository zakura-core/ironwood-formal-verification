import Zcash.Snark.ZeroKnowledge.Sampling
import Zcash.Common.UniformMeasure

/-!
# Zero-denominator probabilities for the product stage

The lookup denominators have factors `B + beta` and `T + gamma`; permutation factors
have the form `value + beta * sigma + gamma`. All offsets and slopes must be fixed
before the two product challenges are drawn. A random private prefix is allowed,
provided those challenge draws are independent of it.

The finite-family bound is one uniform field atom per factor, plus the two wide-
reduction biases. Relating these families to the concrete row constructors, and then
to the joint prover's invalid-row event, remains a separate obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder card_Fp)
open Zcash.Common
open scoped ENNReal

/-- Product-stage verifier coins, in the order `beta`, `gamma`. -/
abbrev ProductChallengeTape := Fin 2 → Fp

/-- One of the beta-only or gamma-linear denominator factors is zero. -/
def productDenominatorBad {b g : ℕ} (betaOffsets : Fin b → Fp)
    (gammaForms : Fin g → Fp × Fp) (tape : ProductChallengeTape) : Prop :=
  (∃ i, betaOffsets i + tape 0 = 0) ∨
    ∃ j, (gammaForms j).1 + tape 0 * (gammaForms j).2 + tape 1 = 0

private theorem uniformFp_add_zero (offset : Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure {v | offset + v = 0} =
      1 / scalarFieldOrder := by
  have hevent : {v : Fp | offset + v = 0} = {-offset} := by
    ext v
    change offset + v = 0 ↔ v = -offset
    rw [add_comm, add_eq_zero_iff_eq_neg]
  rw [hevent, Zcash.uniformOfFintype_toOuterMeasure_singleton, card_Fp]

/-- Each factor costs at most one atom under independent uniform product challenges. -/
theorem uniformProductDenominator_bad_le {b g : ℕ} (betaOffsets : Fin b → Fp)
    (gammaForms : Fin g → Fp × Fp) :
    (PMF.uniformOfFintype ProductChallengeTape).toOuterMeasure
        {tape | productDenominatorBad betaOffsets gammaForms tape} ≤
      (((b + g : ℕ) : ℝ≥0∞) / scalarFieldOrder) := by
  let event : Fin b ⊕ Fin g → Set ProductChallengeTape := Sum.elim
    (fun i => {tape | betaOffsets i + tape 0 = 0})
    (fun j => {tape | (gammaForms j).1 + tape 0 * (gammaForms j).2 + tape 1 = 0})
  have hevent : {tape | productDenominatorBad betaOffsets gammaForms tape} = ⋃ i, event i := by
    ext tape
    simp [productDenominatorBad, event]
  have hpoint (index : Fin b ⊕ Fin g) :
      (PMF.uniformOfFintype ProductChallengeTape).toOuterMeasure (event index) ≤
        1 / scalarFieldOrder := by
    rcases index with i | j
    · change (PMF.uniformOfFintype ProductChallengeTape).toOuterMeasure
        {tape | tape 0 ∈ {v : Fp | betaOffsets i + v = 0}} ≤ _
      rw [Zcash.uniformOfFintype_point_measure, uniformFp_add_zero]
    · change (PMF.uniformOfFintype ProductChallengeTape).toOuterMeasure
        {tape | tape 1 ∈ {v : Fp | (gammaForms j).1 + tape 0 * (gammaForms j).2 + v = 0}} ≤ _
      apply Zcash.uniformOfFintype_point_mem_blind_le 1
        (fun tape => {v | (gammaForms j).1 + tape 0 * (gammaForms j).2 + v = 0})
      · intro tape value
        simp only [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      · intro tape
        rw [uniformFp_add_zero]
  rw [hevent]
  calc
    _ ≤ ∑ i : Fin b ⊕ Fin g,
        (PMF.uniformOfFintype ProductChallengeTape).toOuterMeasure (event i) :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin b ⊕ Fin g, (1 : ℝ≥0∞) / scalarFieldOrder :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]

/-- Fresh product challenges using the implemented field sampler. -/
noncomputable def wideProductChallenges : PMF ProductChallengeTape :=
  (sampleFieldsWith 2 id).runFreshPMF fieldSample

/-- Wide reduction adds two sample biases to the uniform zero-denominator bound. -/
theorem wideProductDenominator_bad_le {b g : ℕ} (betaOffsets : Fin b → Fp)
    (gammaForms : Fin g → Fp × Fp) :
    wideProductChallenges.toOuterMeasure {tape | productDenominatorBad betaOffsets gammaForms tape} ≤
      (((b + g : ℕ) : ℝ≥0∞) / scalarFieldOrder) + 2 * challenge255Bias := by
  have h := (sampleFieldsWith_error_bound 2 id).1
  rw [PMF.map_id] at h
  exact event_measure_le_of_bias h _ (uniformProductDenominator_bad_le betaOffsets gammaForms)

/-- A random pre-challenge private prefix preserves the same bound when the two coins are fresh. -/
theorem wideProductDenominator_mixture_bad_le {A : Type*} {b g : ℕ} (prefixLaw : PMF A)
    (betaOffsets : A → Fin b → Fp) (gammaForms : A → Fin g → Fp × Fp) :
    (prefixLaw.bind fun state => wideProductChallenges.map (Prod.mk state)).toOuterMeasure
        {view | productDenominatorBad (betaOffsets view.1) (gammaForms view.1) view.2} ≤
      (((b + g : ℕ) : ℝ≥0∞) / scalarFieldOrder) + 2 * challenge255Bias := by
  rw [PMF.toOuterMeasure_bind_apply]
  have hpoint (state : A) :
      (wideProductChallenges.map (Prod.mk state)).toOuterMeasure
          {view | productDenominatorBad (betaOffsets view.1) (gammaForms view.1) view.2} ≤
        (((b + g : ℕ) : ℝ≥0∞) / scalarFieldOrder) + 2 * challenge255Bias := by
    rw [PMF.toOuterMeasure_map_apply]
    exact wideProductDenominator_bad_le (betaOffsets state) (gammaForms state)
  calc
    _ ≤ ∑' state, prefixLaw state *
        ((((b + g : ℕ) : ℝ≥0∞) / scalarFieldOrder) + 2 * challenge255Bias) :=
      ENNReal.tsum_le_tsum fun state => mul_le_mul_right (hpoint state) (prefixLaw state)
    _ = _ := by rw [ENNReal.tsum_mul_right, prefixLaw.tsum_coe, one_mul]

/-- Dense factor counts: three beta-only lookup columns, and fifteen permutation plus
three gamma-only lookup columns, each over 2042 usable rows per Action. -/
theorem widePinnedProductDenominator_bad_le (actions : ℕ)
    (betaOffsets : Fin (3 * actions * 2042) → Fp)
    (gammaForms : Fin (18 * actions * 2042) → Fp × Fp) :
    wideProductChallenges.toOuterMeasure {tape | productDenominatorBad betaOffsets gammaForms tape} ≤
      (((42882 * actions : ℕ) : ℝ≥0∞) / scalarFieldOrder) + 2 * challenge255Bias := by
  have hcount : 3 * actions * 2042 + 18 * actions * 2042 = 42882 * actions := by omega
  simpa only [hcount] using wideProductDenominator_bad_le betaOffsets gammaForms

end Zcash.Snark.ZeroKnowledge
