import Zcash.Snark.Soundness.Oracle.Challenge255

/-!
# The honest prover's field-sampling law

The pinned Ironwood prover specification
<https://gist.githubusercontent.com/ebfull/bf25819afa697e39b54bd5f1a1992a2c/raw/589528c0f752112fd83c42aeeea91b6958e67605/zk.md>
specifies one independent, uniform 512-bit integer per fresh field sample, reduced modulo `p`.
This is the same arithmetic conversion already modeled by `challenge255`; no hashing takes
place in this sampler. Independence and uniformity of the caller's input words are premises
of this distribution model, not properties established about a concrete PRNG.

These are sampling facts. They do not, by themselves, prove or refute zero-knowledge of the
joint proof distribution.
-/

namespace Zcash.Snark.ZeroKnowledge

set_option exponentiation.threshold 1024
set_option maxRecDepth 8192

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- Number of fresh field elements consumed by one attempt with `actions` Actions. -/
def fieldSampleCount (actions : ℕ) : ℕ := 148 * actions + 46

/-- Each field sample consumes eight 64-bit words. -/
def wordSampleCount (actions : ℕ) : ℕ := 8 * fieldSampleCount actions

theorem wordSampleCount_one : wordSampleCount 1 = 1552 := rfl

theorem wordSampleCount_two : wordSampleCount 2 = 2736 := rfl

/-- The implemented field conversion under independent uniform input bits. -/
noncomputable def fieldSample : PMF Fp := challenge255

/-- The separate uniform-field idealization used in algebraic masking arguments. -/
noncomputable def idealFieldSample : PMF Fp := uniformChallenge

/-- Reusing the exact reduction calculation does not introduce a hash assumption. -/
theorem fieldSample_apply (x : Fp) :
    fieldSample x =
      ((challengeQuot + if x.val < challengeRem then 1 else 0 : ℕ) : ℝ≥0∞) /
        (challengeDigestCard : ℕ) :=
  challenge255_apply x

/-- Continuation-weighted comparison, suitable for composition across fresh samples. -/
theorem fieldSample_weightedBias :
    PMFWeightedBiasLE fieldSample idealFieldSample challenge255Bias :=
  challenge255_weightedBias_le

/-- The existing exact arithmetic bound applies to the prover's samples too. -/
theorem fieldSample_bias_le : challenge255Bias ≤ 1 / 2 ^ 260 :=
  challenge255Bias_le

/-- The remainder is nonzero: wide reduction is not an exact uniform sampler. -/
theorem fieldSample_remainder_pos : 0 < challengeRem := by
  norm_num [challengeRem, challengeDigestCard, scalarFieldOrder,
    CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- A heavy residue and a light residue have strictly different probabilities. -/
theorem fieldSample_zero_gt_light : fieldSample (challengeRem : Fp) < fieldSample 0 := by
  have hrem : challengeRem < scalarFieldOrder :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))
  have hzero : (0 : Fp).val < challengeRem := fieldSample_remainder_pos
  have hlight : ¬ (challengeRem : Fp).val < challengeRem := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrem]
    exact lt_irrefl _
  rw [fieldSample_apply, fieldSample_apply, if_neg hlight, if_pos hzero, Nat.add_zero]
  apply ENNReal.div_lt_div_right
    (Nat.cast_ne_zero.mpr (NeZero.ne challengeDigestCard)) (ENNReal.natCast_ne_top _)
  exact_mod_cast Nat.lt_succ_self challengeQuot

/-- An ideal uniform-field theorem cannot be identified with the deployed sampling law. -/
theorem fieldSample_ne_ideal : fieldSample ≠ idealFieldSample := by
  intro h
  have hstrict := fieldSample_zero_gt_light
  rw [h] at hstrict
  simp only [idealFieldSample, uniformChallenge, PMF.uniformOfFintype_apply,
    lt_self_iff_false] at hstrict

/-- Every field value remains possible under wide reduction, including exceptional challenges. -/
theorem fieldSample_ne_zero (x : Fp) : fieldSample x ≠ 0 := by
  change x ∈ challenge255.support
  rw [challenge255, PMF.mem_support_map_iff]
  have hsize : scalarFieldOrder < challengeDigestCard := by
    norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD, challengeDigestCard]
  refine ⟨⟨x.val, lt_trans (ZMod.val_lt x) hsize⟩,
    PMF.mem_support_uniformOfFintype _, ?_⟩
  exact ZMod.natCast_zmod_val x

end Zcash.Snark.ZeroKnowledge
