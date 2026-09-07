import Zcash.Snark.ZeroKnowledge.PlonkAttempt
import Zcash.Snark.ZeroKnowledge.PlonkPoints

/-!
# Identity failures in the observed full proof

Every point in the verifier's message schedule comes from the independently blinded
pre-IPA vector or the IPA point family. This connects the ideal point bounds to the
actual typed proof law, then charges the full private tape's wide-reduction bias.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

private theorem point_not_mem_absorbPermSet {F G : Type*} (point : G) (evals : PermSetEval F) :
    TranscriptElt.point point ∉ absorbPermSet evals := by
  cases h : evals.lastEval <;> simp [absorbPermSet, h]

private theorem point_not_mem_absorbLookup {F G : Type*} (point : G) (evals : LookupEval F) :
    TranscriptElt.point point ∉ absorbLookup evals := by
  simp [absorbLookup]

/-- Nonidentity source commitments supply nonidentity points in every emitted proof slot. -/
theorem plonkProofString_no_identity {actions k : ℕ} {F G : Type*} [Zero G]
    (instances : Fin actions → F) (fixed : Fin 29 → F) (sigma : Fin 15 → F)
    (column : PrivateColumnId actions → Fin 4 → F)
    (points : Fin (22 * actions + 10) → G) (rEval : F) (groupValues : Fin 5 → F)
    (tail : IpaTranscript k F G)
    (hpoints : ∀ i, points i ≠ 0) (htail : ∀ i, tail.pointFamily i ≠ 0) :
    TranscriptElt.point 0 ∉ plonkAttemptTrace
      (plonkProofString instances fixed sigma column points rEval groupValues tail) := by
  have hmask : tail.maskCommitment ≠ 0 := htail (.inl ())
  have hpointZero (i) : (0 : G) ≠ points i := (hpoints i).symm
  have hleft (j : Fin k) : (0 : G) ≠ (tail.messages j).1 := (htail (.inr (j, false))).symm
  have hright (j : Fin k) : (0 : G) ≠ (tail.messages j).2 := (htail (.inr (j, true))).symm
  simp [plonkAttemptTrace, preIpaTranscript, absorbPoints2, absorbPoints, absorbLookupPermuted,
    absorbScalars2, absorbScalars, point_not_mem_absorbPermSet, point_not_mem_absorbLookup,
    plonkProofString, plonkColumnEntry, plonkLinearEntry, plonkPieceEntry, plonkQuotientPrimeEntry,
    hpointZero, hmask, hleft, hright, eq_comm]

/-- An identity encountered by the encoded observer belongs to one of the bounded source families. -/
theorem plonkProofFromJointView_identity_imp {actions k : ℕ} {G : Type*} [Zero G]
    (pub : PlonkPublicPolynomials actions) (x x1 : Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (h : TranscriptElt.point 0 ∈ plonkAttemptTrace (plonkProofFromJointView pub x x1 view)) :
    plonkJointPointFailure view := by
  by_contra hgood
  have hparts : (∀ i, view.1.1 i ≠ 0) ∧ ∀ i, view.2.pointFamily i ≠ 0 := by
    simpa only [plonkJointPointFailure, not_or, not_exists] using hgood
  exact plonkProofString_no_identity _ _ _ _ _ _ _ _ hparts.1 hparts.2 h

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- Identity points in the actual typed proof cost at most their ideal bound plus tape bias. -/
theorem sampledPlonkVerifier_identity_le {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (sampledPlonkVerifierProver construct history urs vk pub ch).toOuterMeasure
        {proof | TranscriptElt.point 0 ∈ plonkAttemptTrace proof} ≤
      (((22 * actions + 2 * urs.k + 11 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (fieldSampleCount actions : ℕ) * challenge255Bias := by
  have hsample := (sampledPlonkJoint_sampling_error_bound construct history urs hk pub
    ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z ch.ipaRound (plonkHonestQuotientPieces vk pub ch)).1
  have hbound := event_measure_le_of_bias hsample {view | plonkJointPointFailure view}
    (idealPlonkJoint_identity_le construct history urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
      ch.ipaRound (plonkHonestQuotientPieces vk pub ch) hW)
  let actual := sampledPlonkJointProver construct history urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
    ch.ipaRound (plonkHonestQuotientPieces vk pub ch)
  have hsubset :
      (plonkProofFromJointView (k := urs.k) (G := G) pub ch.x ch.x1) ⁻¹'
          {proof | TranscriptElt.point 0 ∈ plonkAttemptTrace proof} ⊆
        {view | plonkJointPointFailure view} := by
    intro view h
    exact plonkProofFromJointView_identity_imp pub ch.x ch.x1 view h
  rw [sampledPlonkVerifierProver, PMF.toOuterMeasure_map_apply]
  exact (actual.toOuterMeasure.mono hsubset).trans hbound

/-- Averaging over the fresh verifier tape preserves the same identity-point bound. -/
theorem freshSampledPlonkVerifier_identity_le {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (law : PMF (Challenges urs.k Fp))
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (freshSampledPlonkVerifierProver urs law construct history vk pub).toOuterMeasure
        {view | TranscriptElt.point 0 ∈ plonkAttemptTrace view.2} ≤
      (((22 * actions + 2 * urs.k + 11 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (fieldSampleCount actions : ℕ) * challenge255Bias := by
  rw [freshSampledPlonkVerifierProver, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  calc
    _ ≤ ∑' ch, law ch * ((((22 * actions + 2 * urs.k + 11 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (fieldSampleCount actions : ℕ) * challenge255Bias) := by
      apply ENNReal.tsum_le_tsum
      intro ch
      exact mul_le_mul_right (sampledPlonkVerifier_identity_le (construct ch) history urs hk vk pub ch hW) _
    _ = _ := by rw [ENNReal.tsum_mul_right, law.tsum_coe, one_mul]

end Zcash.Snark.ZeroKnowledge
