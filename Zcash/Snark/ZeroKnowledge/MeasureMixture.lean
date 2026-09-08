import Zcash.Snark.ZeroKnowledge.MeasureEventBias

/-!
# Discrete seed mixtures of complete observation laws

A fresh seed selects a probability measure on an infinite observation space.
This construction keeps the seed independent of the subsequent tape experiment;
it does not replace the infinite stream by a discrete probability mass function.
-/

namespace Zcash.Snark.ZeroKnowledge

open MeasureTheory Zcash.Common
open scoped ENNReal

/-- First sample a discrete seed, then run its complete observation experiment. -/
noncomputable def pmfMeasureMixture {Seed A : Type*} [MeasurableSpace A]
    (source : PMF Seed) (family : Seed → Measure A) : Measure A :=
  Measure.sum (fun seed => source seed • family seed)

/-- Measurable event probabilities are the exact seed-weighted sums. -/
theorem pmfMeasureMixture_apply {Seed A : Type*} [MeasurableSpace A]
    (source : PMF Seed) (family : Seed → Measure A) (event : Set A)
    (hmeasurable : MeasurableSet event) :
    pmfMeasureMixture source family event = ∑' seed, source seed * family seed event := by
  simp only [pmfMeasureMixture, Measure.sum_apply _ hmeasurable, Measure.smul_apply,
    smul_eq_mul]

/-- Normalized component experiments give a normalized seeded experiment. -/
instance pmfMeasureMixture_isProbabilityMeasure {Seed A : Type*} [MeasurableSpace A]
    (source : PMF Seed) (family : Seed → Measure A)
    [∀ seed, IsProbabilityMeasure (family seed)] :
    IsProbabilityMeasure (pmfMeasureMixture source family) := by
  constructor
  simp only [pmfMeasureMixture_apply _ _ _ MeasurableSet.univ, measure_univ,
    mul_one, PMF.tsum_coe]

/-- An unused seed has no effect on the complete observation law. -/
theorem pmfMeasureMixture_const {Seed A : Type*} [MeasurableSpace A]
    (source : PMF Seed) (law : Measure A) :
    pmfMeasureMixture source (fun _ => law) = law := by
  ext event he
  rw [pmfMeasureMixture_apply _ _ _ he, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Common measurable observations commute with sampling the fresh seed. -/
theorem pmfMeasureMixture_map {Seed A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (source : PMF Seed) (family : Seed → Measure A) (observe : A → B)
    (hmeasurable : Measurable observe) :
    (pmfMeasureMixture source family).map observe =
      pmfMeasureMixture source (fun seed => (family seed).map observe) := by
  ext event he
  rw [Measure.map_apply hmeasurable he, pmfMeasureMixture_apply _ _ _ (he.preimage hmeasurable),
    pmfMeasureMixture_apply _ _ _ he]
  exact tsum_congr (fun seed => by rw [Measure.map_apply hmeasurable he])

/-- On discrete output experiments, the mixture is exactly the existing PMF bind. -/
theorem pmfMeasureMixture_toMeasure {Seed A : Type*} [MeasurableSpace A]
    (source : PMF Seed) (family : Seed → PMF A) :
    pmfMeasureMixture source (fun seed => (family seed).toMeasure) =
      (source.bind family).toMeasure := by
  ext event he
  rw [pmfMeasureMixture_apply _ _ _ he, PMF.toMeasure_bind_apply _ _ _ he]

/-- A common seed mixture preserves a uniform conditional event bound. -/
theorem measureEventBias_mixture {Seed A : Type*} [MeasurableSpace A]
    (source : PMF Seed) (actual ideal : Seed → Measure A) (error : ℝ≥0∞)
    (h : ∀ seed, MeasureEventBiasLE (actual seed) (ideal seed) error) :
    MeasureEventBiasLE (pmfMeasureMixture source actual) (pmfMeasureMixture source ideal) error := by
  intro event he
  rw [pmfMeasureMixture_apply _ _ _ he, pmfMeasureMixture_apply _ _ _ he]
  calc
    (∑' seed, source seed * actual seed event) ≤ ∑' seed, source seed * (ideal seed event + error) :=
      ENNReal.tsum_le_tsum (fun seed => mul_le_mul_right (h seed event he) _)
    _ = (∑' seed, source seed * ideal seed event) + error := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Seed-dependent errors are averaged under the actual seed law, without a worst-seed assumption. -/
theorem measureEventBias_mixture_average {Seed A : Type*} [MeasurableSpace A]
    (source : PMF Seed) (actual ideal : Seed → Measure A) (error : Seed → ℝ≥0∞)
    (h : ∀ seed, MeasureEventBiasLE (actual seed) (ideal seed) (error seed)) :
    MeasureEventBiasLE (pmfMeasureMixture source actual) (pmfMeasureMixture source ideal)
      (∑' seed, source seed * error seed) := by
  intro event he
  rw [pmfMeasureMixture_apply _ _ _ he, pmfMeasureMixture_apply _ _ _ he]
  calc
    (∑' seed, source seed * actual seed event) ≤ ∑' seed, source seed * (ideal seed event + error seed) :=
      ENNReal.tsum_le_tsum (fun seed => mul_le_mul_right (h seed event he) _)
    _ = _ := by simp only [mul_add, ENNReal.tsum_add]

end Zcash.Snark.ZeroKnowledge
