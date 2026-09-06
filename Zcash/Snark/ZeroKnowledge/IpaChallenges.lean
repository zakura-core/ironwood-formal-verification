import Zcash.Snark.ZeroKnowledge.IpaTranscript
import Zcash.Snark.ZeroKnowledge.Sampling

/-!
# Fresh IPA challenges and the probability of a zero challenge

The interactive schedule receives `xi`, then `z`, then one challenge per round. The
simulation requires `xi` and the round challenges to be nonzero; it permits `z = 0`.
This file prices that event for independent verifier coins. It does not model a hash
query or infer independence of Fiat–Shamir challenges from the proof transcript.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder card_Fp)
open Zcash.Common
open scoped ENNReal

/-- The verifier's coins in challenge order: `xi`, `z`, and the `k` folding challenges. -/
abbrev IpaChallengeTape (k : ℕ) (F : Type*) := Fin (k + 2) → F

/-- Supply an independently sampled challenge tape to the existing IPA computation. -/
def IpaPublic.withChallenges {k : ℕ} {F G : Type*} (pub : IpaPublic k F G)
    (challenges : IpaChallengeTape k F) : IpaPublic k F G :=
  { pub with
    xi := challenges 0
    z := challenges 1
    rounds := fun j => challenges j.succ.succ }

/-- The nonzero premises actually used by the algebraic simulator; `z` is unrestricted. -/
def IpaChallengesNonzero {k : ℕ} {F : Type*} [Zero F]
    (challenges : IpaChallengeTape k F) : Prop :=
  challenges 0 ≠ 0 ∧ ∀ j : Fin k, challenges j.succ.succ ≠ 0

instance {k : ℕ} {F : Type*} [Zero F] [DecidableEq F] :
    DecidablePred (IpaChallengesNonzero (k := k) (F := F)) := fun challenges =>
  inferInstanceAs (Decidable (challenges 0 ≠ 0 ∧ ∀ j : Fin k, challenges j.succ.succ ≠ 0))

/-- Select `xi` and the folding challenges, skipping the unrestricted `z` slot. -/
def ipaNonzeroChallengeIndex (k : ℕ) : Fin (k + 1) → Fin (k + 2) :=
  Fin.cases 0 (fun j => j.succ.succ)

/-- A union bound on the `k+1` challenge coordinates required to be nonzero. -/
theorem ipaChallenges_bad_le {k : ℕ} (law : PMF (IpaChallengeTape k Fp)) (ε : ℝ≥0∞)
    (hatom : ∀ i : Fin (k + 1),
      law.toOuterMeasure {challenges | challenges (ipaNonzeroChallengeIndex k i) = 0} ≤ ε) :
    law.toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges} ≤
      ((k + 1 : ℕ) : ℝ≥0∞) * ε := by
  have hevent : {challenges : IpaChallengeTape k Fp | ¬ IpaChallengesNonzero challenges} =
      ⋃ i : Fin (k + 1), {challenges | challenges (ipaNonzeroChallengeIndex k i) = 0} := by
    ext challenges
    by_cases hzero : challenges 0 = 0 <;>
      simp [IpaChallengesNonzero, ipaNonzeroChallengeIndex, Fin.exists_fin_succ, hzero]
  rw [hevent]
  calc
    _ ≤ ∑ i : Fin (k + 1),
        law.toOuterMeasure {challenges | challenges (ipaNonzeroChallengeIndex k i) = 0} :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin (k + 1), ε := Finset.sum_le_sum fun i _ => hatom i
    _ = _ := by simp [nsmul_eq_mul]

/-- Under uniform independent verifier challenges, the bad event costs at most `(k+1)/p`. -/
theorem uniformIpaChallenges_bad_le (k : ℕ) :
    (PMF.uniformOfFintype (IpaChallengeTape k Fp)).toOuterMeasure
        {challenges | ¬ IpaChallengesNonzero challenges} ≤
      ((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
  rw [div_eq_mul_inv]
  apply ipaChallenges_bad_le
  intro i
  change (PMF.uniformOfFintype (IpaChallengeTape k Fp)).toOuterMeasure
      ((fun challenges => challenges (ipaNonzeroChallengeIndex k i)) ⁻¹' {0}) ≤ _
  rw [← PMF.toOuterMeasure_map_apply, Zcash.map_eval_uniformOfFintype,
    PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, card_Fp]

/-- Fresh verifier samples using the same wide reduction, independently of the prover's coins. -/
noncomputable def wideIpaChallenges (k : ℕ) : PMF (IpaChallengeTape k Fp) :=
  (sampleFieldsWith (k + 2) id).runFreshPMF fieldSample

/-- The wide-reduced verifier law has the same zero-event bound plus its sampling bias.

Replacing all `k+2` samples is a conservative bound; only `k+1` are required nonzero. -/
theorem wideIpaChallenges_bad_le (k : ℕ) :
    (wideIpaChallenges k).toOuterMeasure {challenges | ¬ IpaChallengesNonzero challenges} ≤
      ((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
        ((k + 2 : ℕ) : ℝ≥0∞) * challenge255Bias := by
  have h := (sampleFieldsWith_error_bound (k + 2) id).1
  rw [PMF.map_id] at h
  exact event_measure_le_of_bias h _ (uniformIpaChallenges_bad_le k)

end Zcash.Snark.ZeroKnowledge
