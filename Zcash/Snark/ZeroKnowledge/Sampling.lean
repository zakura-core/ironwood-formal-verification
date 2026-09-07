import Zcash.Snark.ZeroKnowledge.Randomness
import Zcash.Common.RelationProbabilityCoins

/-!
# Replacing the prover's complete randomness tape

For an arbitrary deterministic continuation, replacing all fresh samples by ideal uniform
field samples changes event probabilities by at most the number of samples times the
one-sample reduction bias. The continuation may include commitments, Fiat–Shamir hashing,
serialization, and errors. Consequently this comparison does not silently condition on
successful proving, nor does it idealize the hash function.

The continuation still needs to be instantiated with, and related to, the honest prover.
The bound below is the sampler-composition lemma, not an assertion that this has happened.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

/-- Split a flat tape into two consecutive blocks without changing its entries. -/
def splitTapeEquiv (m n : ℕ) (F : Type*) :
    (Fin (m + n) → F) ≃ ((Fin m → F) × (Fin n → F)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl F)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) F)

/-- Continuation-weighted bias between normalized finite laws is symmetric. -/
theorem weightedBias_symm {F : Type*} [Fintype F] {actual ideal : PMF F} {ε : ℝ≥0∞}
    (h : PMFWeightedBiasLE actual ideal ε) : PMFWeightedBiasLE ideal actual ε := by
  intro weight hweight
  have split (law : PMF F) :
      (∑ x, law x * weight x) + (∑ x, law x * (1 - weight x)) = 1 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add, add_tsub_cancel_of_le (hweight _), mul_one]
    simpa only [tsum_fintype] using law.tsum_coe
  have hcomplement := h (fun x => 1 - weight x) (fun _ => tsub_le_self)
  have hsum :
      (∑ x, ideal x * weight x) + 1 ≤
        ((∑ x, actual x * weight x) + ε) + 1 := by
    calc
      (∑ x, ideal x * weight x) + 1 =
          (∑ x, ideal x * weight x) +
            ((∑ x, actual x * weight x) + (∑ x, actual x * (1 - weight x))) := by
              rw [split actual]
      _ ≤ (∑ x, ideal x * weight x) +
            ((∑ x, actual x * weight x) + ((∑ x, ideal x * (1 - weight x)) + ε)) :=
              add_le_add le_rfl (add_le_add le_rfl hcomplement)
      _ = ((∑ x, actual x * weight x) + ε) +
            ((∑ x, ideal x * weight x) + (∑ x, ideal x * (1 - weight x))) := by
              ac_rfl
      _ = ((∑ x, actual x * weight x) + ε) + 1 := by rw [split ideal]
  exact (ENNReal.add_le_add_iff_right (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).mp hsum

/-- Draw exactly `count` fresh field values, then run the supplied continuation. -/
def sampleFieldsWith {A : Type*} : (count : ℕ) → ((Fin count → Fp) → A) → OracleComp Unit Fp A
  | 0, finish => .pure (finish Fin.elim0)
  | count + 1, finish => .query () fun value =>
      sampleFieldsWith count (fun rest => finish (Fin.cons value rest))

/-- The sampling program's query count is derived from its definition. -/
theorem sampleFieldsWith_queryBound {A : Type*} (count : ℕ)
    (finish : (Fin count → Fp) → A) :
    (sampleFieldsWith count finish).QueryBound count := by
  induction count with
  | zero => exact .pure _ 0
  | succ count ih => exact .query fun value => ih _

/-- A deterministic observation of the result commutes with running the field sampler. -/
theorem sampleFieldsWith_map {A B : Type*} (count : ℕ)
    (finish : (Fin count → Fp) → A) (observe : A → B) (law : PMF Fp) :
    (sampleFieldsWith count (observe ∘ finish)).runFreshPMF law =
      ((sampleFieldsWith count finish).runFreshPMF law).map observe := by
  induction count with
  | zero => simp [sampleFieldsWith, OracleComp.runFreshPMF, PMF.map, Function.comp_def]
  | succ count ih =>
    change law.bind (fun value =>
        (sampleFieldsWith count (fun rest => observe (finish (Fin.cons value rest)))).runFreshPMF law) =
      (law.bind (fun value =>
        (sampleFieldsWith count (fun rest => finish (Fin.cons value rest))).runFreshPMF law)).map observe
    rw [PMF.map_bind]
    congr 1
    funext value
    exact ih (fun rest => finish (Fin.cons value rest))

/-- Discarding a fixed number of fresh draws preserves a constant result exactly. -/
theorem sampleFieldsWith_const {A : Type*} (count : ℕ) (value : A) (law : PMF Fp) :
    (sampleFieldsWith count (fun _ => value)).runFreshPMF law = PMF.pure value := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change law.bind (fun _ => (sampleFieldsWith count (fun _ => value)).runFreshPMF law) = _
    simp_rw [ih]
    exact PMF.bind_const _ _

/-- Each coordinate of the independent tape has the supplied field law exactly. -/
theorem sampleFieldsWith_coordinate (count : ℕ) (index : Fin count) (law : PMF Fp) :
    (sampleFieldsWith count (fun tape => tape index)).runFreshPMF law = law := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
    refine Fin.cases ?_ (fun j => ?_) index
    · change law.bind (fun value => (sampleFieldsWith count (fun _ => value)).runFreshPMF law) = law
      simp_rw [sampleFieldsWith_const]
      exact PMF.bind_pure _
    · change law.bind (fun _ => (sampleFieldsWith count (fun rest => rest j)).runFreshPMF law) = law
      rw [ih j]
      exact PMF.bind_const _ _

/-- Independent ideal draws are the uniform law on the complete field tape. -/
theorem sampleFieldsWith_uniform {A : Type*} (count : ℕ)
    (finish : (Fin count → Fp) → A) :
    (sampleFieldsWith count finish).runFreshPMF idealFieldSample =
      (PMF.uniformOfFintype (Fin count → Fp)).map finish := by
  induction count with
  | zero =>
    change PMF.pure (finish Fin.elim0) = _
    have hconst : finish = fun _ => finish Fin.elim0 := by
      funext tape
      exact congrArg finish (Subsingleton.elim tape Fin.elim0)
    conv_rhs => rw [hconst]
    exact (PMF.map_const _ _).symm
  | succ count ih =>
    change idealFieldSample.bind (fun value =>
      (sampleFieldsWith count (fun rest => finish (Fin.cons value rest))).runFreshPMF
        idealFieldSample) = _
    simp_rw [ih]
    let e := Fin.consEquiv (fun _ : Fin (count + 1) => Fp)
    calc
      _ = (Zcash.independentProductPMF (PMF.uniformOfFintype Fp)
          (PMF.uniformOfFintype (Fin count → Fp))).map (finish ∘ e) := by
        simp only [Zcash.independentProductPMF, PMF.map_bind, PMF.map_comp]
        rfl
      _ = _ := by
        rw [Zcash.independentProductPMF_uniform, ← PMF.map_comp,
          Zcash.map_uniformOfFintype_equiv]

/-- Any computation on `count` implemented samples is close to the same computation on a
uniform field tape. No property of the deterministic continuation is assumed. -/
theorem sampleFieldsWith_error_bound {A : Type*} (count : ℕ)
    (finish : (Fin count → Fp) → A) :
    PMFEventBiasLE ((sampleFieldsWith count finish).runFreshPMF fieldSample)
        ((PMF.uniformOfFintype (Fin count → Fp)).map finish) (count * challenge255Bias) ∧
      PMFEventBiasLE ((PMF.uniformOfFintype (Fin count → Fp)).map finish)
        ((sampleFieldsWith count finish).runFreshPMF fieldSample) (count * challenge255Bias) := by
  rw [← sampleFieldsWith_uniform]
  constructor
  · exact OracleComp.runFreshPMF_eventBiasLE fieldSample_weightedBias
      (sampleFieldsWith_queryBound count finish)
  · exact OracleComp.runFreshPMF_eventBiasLE (weightedBias_symm fieldSample_weightedBias)
      (sampleFieldsWith_queryBound count finish)

/-- Implemented-law execution of one complete attempt, including whatever result it returns. -/
noncomputable def sampledAttempt {A : Type*} (actions : ℕ)
    (finish : (Fin (fieldSampleCount actions) → Fp) → A) : PMF A :=
  (sampleFieldsWith (fieldSampleCount actions) finish).runFreshPMF fieldSample

/-- The same continuation with only its blinding-field sampler idealized. -/
noncomputable def idealSampledAttempt {A : Type*} (actions : ℕ)
    (finish : (Fin (fieldSampleCount actions) → Fp) → A) : PMF A :=
  (sampleFieldsWith (fieldSampleCount actions) finish).runFreshPMF idealFieldSample

/-- Two-sided event comparison of the entire attempt, with no success conditioning. -/
theorem sampledAttempt_error_bound {A : Type*} (actions : ℕ)
    (finish : (Fin (fieldSampleCount actions) → Fp) → A) :
    PMFEventBiasLE (sampledAttempt actions finish) (idealSampledAttempt actions finish)
        (fieldSampleCount actions * challenge255Bias) ∧
      PMFEventBiasLE (idealSampledAttempt actions finish) (sampledAttempt actions finish)
        (fieldSampleCount actions * challenge255Bias) := by
  constructor
  · exact OracleComp.runFreshPMF_eventBiasLE fieldSample_weightedBias
      (sampleFieldsWith_queryBound _ _)
  · exact OracleComp.runFreshPMF_eventBiasLE (weightedBias_symm fieldSample_weightedBias)
      (sampleFieldsWith_queryBound _ _)

end Zcash.Snark.ZeroKnowledge
