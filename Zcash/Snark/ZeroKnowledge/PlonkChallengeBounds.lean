import Zcash.Snark.ZeroKnowledge.PlonkChallengePoints
import Zcash.Common.UniformMeasure

/-!
# Probability of exceptional public challenges

The union bound counts `x = 0`, `xi = 0`, zero IPA round challenges, two opportunities
to hit the size-2048 domain, and four collisions between `q` and a rotated `x`.
For independent uniform verifier coins it is `(k + 4102)/p`. Wide reduction adds
`(k + 11)` one-sample biases. These bounds do not include invalid private rows,
serialization failures, or Fiat–Shamir queries.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf scalarFieldOrder card_Fp)
open Zcash.Common
open scoped ENNReal

/-- Zero coordinates, domain hits for `x`, domain hits for `q`, and point collisions. -/
abbrev PlonkBadChallengeIndex (k : ℕ) :=
  Fin (k + 2) ⊕ Fin 2048 ⊕ Fin 2048 ⊕ Fin 4

/-- One event in the finite cover of all challenge configurations outside the proven region. -/
def plonkChallengeBadEvent {k : ℕ} (index : PlonkBadChallengeIndex k)
    (tape : PlonkChallengeTape k Fp) : Prop :=
  let ch := plonkChallengesFromTape tape
  match index with
  | .inl i => Fin.cases ch.x (Fin.cases ch.xi ch.ipaRound) i = (0 : Fp)
  | .inr (.inl row) => ch.x = omegaOf 11 ^ row.val
  | .inr (.inr (.inl row)) => ch.x3 = omegaOf 11 ^ row.val
  | .inr (.inr (.inr i)) => ch.x3 = ch.x * omegaOf 11 ^ (plonkRotationExponent i).val

/-- Every challenge configuration not covered by simulation lies in the finite bad-event union. -/
theorem plonkChallenges_bad_cover (k : ℕ) :
    {tape : PlonkChallengeTape k Fp | ¬ PlonkChallengesGood (plonkChallengesFromTape tape)} ⊆
      ⋃ i : PlonkBadChallengeIndex k, {tape | plonkChallengeBadEvent i tape} := by
  intro tape hbad
  by_contra h
  have hnone (i : PlonkBadChallengeIndex k) : ¬ plonkChallengeBadEvent i tape :=
    fun hi => h (Set.mem_iUnion.mpr ⟨i, hi⟩)
  apply hbad
  apply plonkChallengesGood_of_simple
  · exact hnone (.inl (Fin.succ ⟨0, by omega⟩))
  · intro j
    exact hnone (.inl j.succ.succ)
  · exact hnone (.inl ⟨0, by omega⟩)
  · intro hx
    have hroot : IsPrimitiveRoot (omegaOf 11) 2048 :=
      omegaOf_primitiveRoot 11 (by decide)
    obtain ⟨i, hi, hpow⟩ := hroot.eq_pow_of_pow_eq_one hx
    exact hnone (.inr (.inl ⟨i, hi⟩)) hpow.symm
  · intro hq
    have hroot : IsPrimitiveRoot (omegaOf 11) 2048 :=
      omegaOf_primitiveRoot 11 (by decide)
    obtain ⟨i, hi, hpow⟩ := hroot.eq_pow_of_pow_eq_one hq
    exact hnone (.inr (.inr (.inl ⟨i, hi⟩))) hpow.symm
  · intro i
    exact hnone (.inr (.inr (.inr i)))

/-- One coordinate of a uniform challenge tape hits a fixed value with probability `1/p`, pricing
exceptional scalar values. -/
private theorem uniformPlonkTape_atom (k : ℕ) (i : Fin (k + 11)) (value : Fp) :
    (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
      {tape | tape i = value} = 1 / scalarFieldOrder := by
  change (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
    ((fun tape => tape i) ⁻¹' {value}) = _
  rw [← PMF.toOuterMeasure_map_apply, Zcash.map_eval_uniformOfFintype,
    Zcash.uniformOfFintype_toOuterMeasure_singleton, card_Fp]

/-- Distinct uniform challenge coordinates satisfy a prescribed functional relation with probability
at most `1/p`, pricing challenge collisions. -/
private theorem uniformPlonkTape_collision (k : ℕ) (i j : Fin (k + 11)) (hij : i ≠ j)
    (f : Fp → Fp) :
    (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
      {tape | tape j = f (tape i)} ≤ 1 / scalarFieldOrder := by
  change (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
    {tape | tape j ∈ ({f (tape i)} : Set Fp)} ≤ _
  apply Zcash.uniformOfFintype_point_mem_blind_le j (fun tape => {f (tape i)})
  · intro tape value
    simp only [Function.update_of_ne hij]
  · intro tape
    rw [Zcash.uniformOfFintype_toOuterMeasure_singleton, card_Fp]

/-- Each indexed event costs at most one uniform field atom. -/
theorem uniformPlonkChallengeBadEvent_le (k : ℕ) (index : PlonkBadChallengeIndex k) :
    (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
      {tape | plonkChallengeBadEvent index tape} ≤ 1 / scalarFieldOrder := by
  rcases index with i | row | row | i
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact (uniformPlonkTape_atom k ⟨4, by omega⟩ 0).le
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact (uniformPlonkTape_atom k ⟨9, by omega⟩ 0).le
      · exact (uniformPlonkTape_atom k ⟨11 + j.val, by omega⟩ 0).le
  · exact (uniformPlonkTape_atom k ⟨4, by omega⟩ (omegaOf 11 ^ row.val)).le
  · exact (uniformPlonkTape_atom k ⟨7, by omega⟩ (omegaOf 11 ^ row.val)).le
  · exact uniformPlonkTape_collision k ⟨4, by omega⟩ ⟨7, by omega⟩
      (by
        intro h
        have hval : (4 : ℕ) = 7 := congrArg (fun t : Fin (k + 11) => t.val) h
        omega)
      (fun x => x * omegaOf 11 ^ (plonkRotationExponent i).val)

/-- Independent uniform verifier coins give the explicit `(k+4102)/p` challenge bound. -/
theorem uniformPlonkChallenges_bad_le (k : ℕ) :
    (uniformPlonkChallenges k).toOuterMeasure {ch | ¬ PlonkChallengesGood ch} ≤
      (((k + 4102 : ℕ) : ℝ≥0∞) / scalarFieldOrder) := by
  rw [uniformPlonkChallenges, PMF.toOuterMeasure_map_apply]
  calc
    _ ≤ (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
        (⋃ i : PlonkBadChallengeIndex k, {tape | plonkChallengeBadEvent i tape}) :=
      MeasureTheory.measure_mono (plonkChallenges_bad_cover k)
    _ ≤ ∑ i : PlonkBadChallengeIndex k,
        (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
          {tape | plonkChallengeBadEvent i tape} :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : PlonkBadChallengeIndex k, (1 : ℝ≥0∞) / scalarFieldOrder :=
      Finset.sum_le_sum fun i _ => uniformPlonkChallengeBadEvent_le k i
    _ = _ := by
      simp [PlonkBadChallengeIndex, nsmul_eq_mul, div_eq_mul_inv, Nat.add_assoc]

/-- Wide-reduced independent verifier coins add the full challenge tape's sampling bias. -/
theorem widePlonkChallenges_bad_le (k : ℕ) :
    (widePlonkChallenges k).toOuterMeasure {ch | ¬ PlonkChallengesGood ch} ≤
      (((k + 4102 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((k + 11 : ℕ) : ℝ≥0∞) * challenge255Bias) :=
  event_measure_le_of_bias (widePlonkChallenges_sampling_error_bound k).1 _
    (uniformPlonkChallenges_bad_le k)

end Zcash.Snark.ZeroKnowledge
