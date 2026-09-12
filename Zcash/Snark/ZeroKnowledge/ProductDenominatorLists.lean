import Zcash.Snark.ZeroKnowledge.ProductDenominators

/-!
# Denominator bounds for computed factor lists

Lists retain repeated factors and therefore give a conservative union bound without
requiring distinct field values. Converting the lists to finite vectors applies the
existing two-challenge sampling theorem to exactly their entries.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- A zero factor in the supplied beta-only offsets or gamma-linear forms. -/
def productDenominatorListBad (betaOffsets : List Fp) (gammaForms : List (Fp × Fp))
    (tape : ProductChallengeTape) : Prop :=
  (∃ offset ∈ betaOffsets, offset + tape 0 = 0) ∨
    ∃ form ∈ gammaForms, form.1 + tape 0 * form.2 + tape 1 = 0

/-- Listing a factor and indexing that same list describe the same bad event. -/
theorem productDenominatorListBad_iff (betaOffsets : List Fp) (gammaForms : List (Fp × Fp))
    (tape : ProductChallengeTape) :
    productDenominatorListBad betaOffsets gammaForms tape ↔
      productDenominatorBad betaOffsets.get gammaForms.get tape := by
  simp only [productDenominatorListBad, productDenominatorBad, List.exists_mem_iff_get]

/-- Each listed factor costs one uniform field atom, plus the two challenge sample biases. -/
theorem wideProductDenominatorList_bad_le (betaOffsets : List Fp) (gammaForms : List (Fp × Fp)) :
    wideProductChallenges.toOuterMeasure {tape | productDenominatorListBad betaOffsets gammaForms tape} ≤
      (((betaOffsets.length + gammaForms.length : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        2 * challenge255Bias := by
  simpa only [productDenominatorListBad_iff] using
    wideProductDenominator_bad_le betaOffsets.get gammaForms.get

end Zcash.Snark.ZeroKnowledge
