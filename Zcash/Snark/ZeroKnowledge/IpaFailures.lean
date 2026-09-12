import Zcash.Snark.ZeroKnowledge.IpaAttempt
import Zcash.Snark.ZeroKnowledge.IpaPoints

/-!
# Success probability of the encoded IPA attempt

The codec premise is precise: it fails exactly on the group identity. A fixed-shape
attempt succeeds exactly when all its points encode and all round challenges are nonzero.
In particular, zero `xi` is not classified as an implementation retry.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder card_Fp)
open Zcash.Common
open scoped ENNReal

/-- The observer's actual success predicate. -/
def ipaSuccessSet {k : ℕ} {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) : Set (IpaFreshView k G) :=
  {view | (observeIpaAttempt pointCodec scalarCodec view).status = .complete}

/-- A round sequence completes exactly when every point write and challenge inversion succeeds. -/
theorem observeIpaRounds_complete_iff {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) (c f : Fp) (rounds : List (Fp × G × G)) :
    (observeIpaRounds pointCodec scalarCodec c f rounds).status = .complete ↔
      ∀ entry ∈ rounds, pointCodec entry.2.1 ≠ none ∧ pointCodec entry.2.2 ≠ none ∧ entry.1 ≠ 0 := by
  induction rounds with
  | nil => simp [observeIpaRounds]
  | cons entry rounds ih =>
    rcases entry with ⟨challenge, left, right⟩
    cases hl : pointCodec left with
    | none => simp [observeIpaRounds, hl]
    | some leftBytes =>
      cases hr : pointCodec right with
      | none => simp [observeIpaRounds, hl, hr]
      | some rightBytes =>
        by_cases hu : challenge = 0 <;> simp [observeIpaRounds, hl, hr, hu, ih]

/-- Success uses the codec's failures and the round challenges, without a test on `xi`. -/
theorem observeIpaAttempt_complete_iff {k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (view : IpaFreshView k G) :
    view ∈ ipaSuccessSet pointCodec scalarCodec ↔
      pointCodec view.2.maskCommitment ≠ none ∧ ∀ j : Fin k,
        pointCodec (view.2.messages j).1 ≠ none ∧ pointCodec (view.2.messages j).2 ≠ none ∧
          view.1 j.succ.succ ≠ 0 := by
  cases hmask : pointCodec view.2.maskCommitment with
  | none => simp [ipaSuccessSet, observeIpaAttempt, hmask]
  | some bytes =>
    simp [ipaSuccessSet, observeIpaAttempt, hmask, observeIpaRounds_complete_iff]

/-- An identity-rejecting codec gives the exact success criterion on algebraic views. -/
theorem ipaSuccess_iff {k : ℕ} {G : Type*} [Zero G]
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0) (view : IpaFreshView k G) :
    view ∈ ipaSuccessSet pointCodec scalarCodec ↔
      (∀ i, view.2.pointFamily i ≠ 0) ∧ (∀ j : Fin k, view.1 j.succ.succ ≠ 0) := by
  rw [observeIpaAttempt_complete_iff]
  simp [hcodec, IpaTranscript.pointFamily, ipaPointFamily, Sum.forall, Bool.forall_bool,
    forall_and, and_assoc, and_comm, and_left_comm]

/-- Uniform independent verifier coins hit zero in a round with probability at most `k/p`. -/
theorem uniformIpaRounds_bad_le (k : ℕ) :
    (PMF.uniformOfFintype (IpaChallengeTape k Fp)).toOuterMeasure
        {challenges | ∃ j : Fin k, challenges j.succ.succ = 0} ≤
      (k : ℝ≥0∞) / scalarFieldOrder := by
  have hevent : {challenges : IpaChallengeTape k Fp | ∃ j : Fin k, challenges j.succ.succ = 0} =
      ⋃ j : Fin k, {challenges | challenges j.succ.succ = 0} := by ext; simp
  have hatom (j : Fin k) :
      (PMF.uniformOfFintype (IpaChallengeTape k Fp)).toOuterMeasure
          {challenges | challenges j.succ.succ = 0} = (scalarFieldOrder : ℝ≥0∞)⁻¹ := by
    change (PMF.uniformOfFintype (IpaChallengeTape k Fp)).toOuterMeasure
      ((fun challenges => challenges j.succ.succ) ⁻¹' {0}) = _
    rw [← PMF.toOuterMeasure_map_apply, Zcash.map_eval_uniformOfFintype,
      PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, card_Fp]
  rw [hevent]
  calc
    _ ≤ ∑ j : Fin k, (PMF.uniformOfFintype (IpaChallengeTape k Fp)).toOuterMeasure
        {challenges | challenges j.succ.succ = 0} := MeasureTheory.measure_iUnion_fintype_le _ _
    _ = _ := by simp [hatom, div_eq_mul_inv, nsmul_eq_mul]

/-- The implemented fresh verifier law adds its sampling error to the zero-round bound. -/
theorem wideIpaRounds_bad_le (k : ℕ) :
    (wideIpaChallenges k).toOuterMeasure {challenges | ∃ j : Fin k, challenges j.succ.succ = 0} ≤
      (k : ℝ≥0∞) / scalarFieldOrder + ((k + 2 : ℕ) : ℝ≥0∞) * challenge255Bias := by
  have h := (sampleFieldsWith_error_bound (k + 2) id).1
  rw [PMF.map_id] at h
  exact event_measure_le_of_bias h _ (uniformIpaRounds_bad_le k)

section Probability

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

omit [Fintype G] in
/-- Reading the verifier tape from the ideal joint experiment recovers its original law. -/
theorem freshIdealIpa_challenges {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) :
    (freshIdealIpaProver law pub coefficients rho).map Prod.fst = law := by
  rw [freshIdealIpaProver, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hconst (challenges : IpaChallengeTape k Fp) :
      (idealIpaProver (pub.withChallenges challenges) coefficients rho).map (fun _ => challenges) =
        PMF.pure challenges := PMF.map_const _ _
  simp_rw [hconst]
  exact PMF.bind_pure law

/-- Identity failures cost at most one inverse group order per emitted point. -/
theorem freshIdealIpa_identity_le {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) :
    (freshIdealIpaProver law pub coefficients rho).toOuterMeasure
        {view | ∃ i, view.2.pointFamily i = 0} ≤
      ((2 * k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
  rw [freshIdealIpaProver, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  calc
    _ ≤ ∑' challenges, law challenges * (((2 * k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder) := by
      apply ENNReal.tsum_le_tsum
      intro challenges
      exact mul_le_mul_right (idealIpa_identity_le (pub.withChallenges challenges) coefficients rho hW) _
    _ = _ := by rw [ENNReal.tsum_mul_right, law.tsum_coe, one_mul]

/-- Ideal honest attempts fail only on an identity point or a zero round challenge. -/
theorem freshIdealIpa_failure_le {k : ℕ} (law : PMF (IpaChallengeTape k Fp))
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) :
    (freshIdealIpaProver law pub coefficients rho).toOuterMeasure
        (ipaSuccessSet pointCodec scalarCodec)ᶜ ≤
      ((2 * k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
        law.toOuterMeasure {challenges | ∃ j : Fin k, challenges j.succ.succ = 0} := by
  have hsubset : (ipaSuccessSet (k := k) pointCodec scalarCodec)ᶜ ⊆
      {view | ∃ i, view.2.pointFamily i = 0} ∪
        {view | ∃ j : Fin k, view.1 j.succ.succ = 0} := by
    intro view hfail
    simp only [Set.mem_compl_iff, ipaSuccess_iff pointCodec scalarCodec hcodec] at hfail
    simpa only [not_and_or, not_forall, not_not, Set.mem_union, Set.mem_setOf_eq] using hfail
  have hrounds : (freshIdealIpaProver law pub coefficients rho).toOuterMeasure
      {view | ∃ j : Fin k, view.1 j.succ.succ = 0} =
      law.toOuterMeasure {challenges | ∃ j : Fin k, challenges j.succ.succ = 0} := by
    change (freshIdealIpaProver law pub coefficients rho).toOuterMeasure
      (Prod.fst ⁻¹' {challenges | ∃ j : Fin k, challenges j.succ.succ = 0}) = _
    rw [← PMF.toOuterMeasure_map_apply, freshIdealIpa_challenges]
  calc
    _ ≤ (freshIdealIpaProver law pub coefficients rho).toOuterMeasure
        ({view | ∃ i, view.2.pointFamily i = 0} ∪
          {view | ∃ j : Fin k, view.1 j.succ.succ = 0}) :=
      (freshIdealIpaProver law pub coefficients rho).toOuterMeasure.mono hsubset
    _ ≤ (freshIdealIpaProver law pub coefficients rho).toOuterMeasure
          {view | ∃ i, view.2.pointFamily i = 0} +
        (freshIdealIpaProver law pub coefficients rho).toOuterMeasure
          {view | ∃ j : Fin k, view.1 j.succ.succ = 0} := MeasureTheory.measure_union_le _ _
    _ ≤ _ := by rw [hrounds]; exact add_le_add (freshIdealIpa_identity_le law pub coefficients rho hW) le_rfl

/-- The wide-reduced honest attempt fails with probability at most `(3k+1)/p + (4k+3) bias`.

At eleven rounds this is `34/p + 47 × bias`. No valid-opening or nonzero-challenge premise
is required for this bound on the fixed-shape attempt observer. -/
theorem wideFreshIpa_failure_le {k : ℕ}
    (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) :
    (freshSampledIpaProver (wideIpaChallenges k) pub coefficients rho).toOuterMeasure
        (ipaSuccessSet pointCodec scalarCodec)ᶜ ≤
      ((3 * k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
        ((4 * k + 3 : ℕ) : ℝ≥0∞) * challenge255Bias := by
  have h := event_measure_le_of_bias
    (freshIpa_sampling_error_bound (wideIpaChallenges k) pub coefficients rho).1 _
    (freshIdealIpa_failure_le (wideIpaChallenges k) pub coefficients rho pointCodec scalarCodec hcodec hW)
  calc
    _ ≤ _ := h
    _ ≤ (((2 * k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder +
          ((k : ℝ≥0∞) / scalarFieldOrder + ((k + 2 : ℕ) : ℝ≥0∞) * challenge255Bias)) +
        ipaSampleCount k * challenge255Bias :=
      add_le_add (add_le_add le_rfl (wideIpaRounds_bad_le k)) le_rfl
    _ = _ := by simp only [ipaSampleCount_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        div_eq_mul_inv]; ring

end Probability

end Zcash.Snark.ZeroKnowledge
