import Zcash.Snark.ZeroKnowledge.PlonkChallengeBounds

/-!
# Challenges which actually stop a prover attempt

Only zero `x` and zero IPA round challenges occur in the attempt's failure tests.
The other exceptional challenges used by simulation are retained by the prover.
The existing per-challenge atom bounds give the smaller failure-only union bound.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- The opening-query failure or a failed IPA challenge inversion. -/
def PlonkFailureChallenges {k : ℕ} (ch : Challenges k Fp) : Prop :=
  ch.x = 0 ∨ ∃ j, ch.ipaRound j = 0

/-- Select the stopping challenges from the larger cover used by the simulation theorem. -/
def plonkFailureChallengeIndex {k : ℕ} (i : Fin (k + 1)) : PlonkBadChallengeIndex k :=
  Fin.cases (.inl ⟨0, by omega⟩) (fun j => .inl j.succ.succ) i

/-- The actual stopping event is covered by `k+1` single-coordinate zero events. -/
theorem plonkFailureChallenges_cover (k : ℕ) :
    {tape : PlonkChallengeTape k Fp | PlonkFailureChallenges (plonkChallengesFromTape tape)} ⊆
      ⋃ i : Fin (k + 1), {tape | plonkChallengeBadEvent (plonkFailureChallengeIndex i) tape} := by
  intro tape h
  rcases h with hx | ⟨j, hj⟩
  · refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
    simpa [plonkFailureChallengeIndex, plonkChallengeBadEvent] using hx
  · exact Set.mem_iUnion.mpr ⟨j.succ, hj⟩

/-- Independent uniform field challenges stop the attempt with probability at most `(k+1)/p`. -/
theorem uniformPlonkFailureChallenges_le (k : ℕ) :
    (uniformPlonkChallenges k).toOuterMeasure {ch | PlonkFailureChallenges ch} ≤
      ((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
  rw [uniformPlonkChallenges, PMF.toOuterMeasure_map_apply]
  calc
    _ ≤ (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
        (⋃ i : Fin (k + 1), {tape | plonkChallengeBadEvent (plonkFailureChallengeIndex i) tape}) :=
      MeasureTheory.measure_mono (plonkFailureChallenges_cover k)
    _ ≤ ∑ i : Fin (k + 1), (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).toOuterMeasure
        {tape | plonkChallengeBadEvent (plonkFailureChallengeIndex i) tape} :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin (k + 1), (1 : ℝ≥0∞) / scalarFieldOrder := by
      apply Finset.sum_le_sum
      intro i _
      exact uniformPlonkChallengeBadEvent_le k (plonkFailureChallengeIndex i)
    _ = _ := by simp [div_eq_mul_inv, nsmul_eq_mul]

/-- Wide reduction adds the full verifier tape's comparison error to the stopping-event bound. -/
theorem widePlonkFailureChallenges_le (k : ℕ) :
    (widePlonkChallenges k).toOuterMeasure {ch | PlonkFailureChallenges ch} ≤
      (((k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        ((k + 11 : ℕ) : ℝ≥0∞) * challenge255Bias :=
  event_measure_le_of_bias (widePlonkChallenges_sampling_error_bound k).1 _
    (uniformPlonkFailureChallenges_le k)

end Zcash.Snark.ZeroKnowledge
