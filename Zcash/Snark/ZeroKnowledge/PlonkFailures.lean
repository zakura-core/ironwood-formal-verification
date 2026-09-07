import Zcash.Snark.ZeroKnowledge.PlonkAttemptPoints
import Zcash.Snark.ZeroKnowledge.PlonkFailureChallenges

/-!
# Probability of failing the full emission schedule

With an identity-rejecting codec, an attempt stops only on an emitted identity,
zero `x`, or a zero IPA round challenge. The bound keeps both the wide-reduced
private tape and the independent wide-reduced verifier tape. No good-challenge,
valid-row, or quotient-agreement premise is needed for this completion bound.

Completion here means finishing the emission schedule, not verifier acceptance.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

/-- The full observer reaches the end of the proof without requesting a retry or returning an error. -/
def plonkAttemptSuccessSet {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8) :
    Set (PlonkFreshView actions k G) :=
  {view | (observePlonkAttempt pointCodec scalarCodec view).status = .complete}

/-- The exact observer's failures are covered by identity points and its stopping challenges. -/
theorem plonkAttempt_failure_subset {actions k : ℕ} {G : Type*} [Zero G]
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0) :
    (plonkAttemptSuccessSet (actions := actions) (k := k) pointCodec scalarCodec)ᶜ ⊆
      {view | TranscriptElt.point 0 ∈ plonkAttemptTrace view.2} ∪
        {view | PlonkFailureChallenges view.1} := by
  intro view hfailed
  by_cases hpoint : TranscriptElt.point 0 ∈ plonkAttemptTrace view.2
  · exact Or.inl hpoint
  · right
    by_contra hch
    have hpoints (point : G) (hmem : .point point ∈ plonkAttemptTrace view.2) : point ≠ 0 := by
      intro hzero
      subst point
      exact hpoint hmem
    have hx : view.1.x ≠ 0 := fun h => hch (Or.inl h)
    have hrounds (j : Fin k) : view.1.ipaRound j ≠ 0 := fun h => hch (Or.inr ⟨j, h⟩)
    exact hfailed ((plonkAttempt_complete_iff pointCodec scalarCodec hcodec view).mpr
      ⟨hpoints, hx, hrounds⟩)

/-- Projecting away every prover message recovers the original independent verifier tape law. -/
theorem freshSampledPlonkVerifier_challenges {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G]
    (urs : URS G) (law : PMF (Challenges urs.k Fp))
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions) :
    (freshSampledPlonkVerifierProver urs law construct history vk pub).map Prod.fst = law := by
  rw [freshSampledPlonkVerifierProver, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hconst (ch : Challenges urs.k Fp) :
      (sampledPlonkVerifierProver (construct ch) history urs vk pub ch).map (fun _ => ch) =
        PMF.pure ch := PMF.map_const _ _
  simp_rw [hconst]
  exact PMF.bind_pure law

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- The complete attempt's failure mass, retaining an arbitrary independent verifier challenge law. -/
theorem freshPlonkAttempt_failure_le {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (law : PMF (Challenges urs.k Fp))
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (freshSampledPlonkVerifierProver urs law construct history vk pub).toOuterMeasure
        (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      ((((22 * actions + 2 * urs.k + 11 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (fieldSampleCount actions : ℕ) * challenge255Bias) +
          law.toOuterMeasure {ch | PlonkFailureChallenges ch} := by
  let actual := freshSampledPlonkVerifierProver urs law construct history vk pub
  have hch : actual.toOuterMeasure {view | PlonkFailureChallenges view.1} =
      law.toOuterMeasure {ch | PlonkFailureChallenges ch} := by
    change actual.toOuterMeasure (Prod.fst ⁻¹' {ch | PlonkFailureChallenges ch}) = _
    rw [← PMF.toOuterMeasure_map_apply]
    dsimp only [actual]
    rw [freshSampledPlonkVerifier_challenges]
  calc
    _ ≤ actual.toOuterMeasure
        ({view | TranscriptElt.point 0 ∈ plonkAttemptTrace view.2} ∪
          {view | PlonkFailureChallenges view.1}) :=
      actual.toOuterMeasure.mono (plonkAttempt_failure_subset pointCodec scalarCodec hcodec)
    _ ≤ actual.toOuterMeasure {view | TranscriptElt.point 0 ∈ plonkAttemptTrace view.2} +
        actual.toOuterMeasure {view | PlonkFailureChallenges view.1} := MeasureTheory.measure_union_le _ _
    _ ≤ _ := by
      rw [hch]
      exact add_le_add (freshSampledPlonkVerifier_identity_le urs hk law construct history vk pub hW) le_rfl

/-- The specified wide-reduced tapes give failure probability at most
`(22m+45)/p + (148m+68) bias` for the eleven-round full attempt. -/
theorem widePlonkAttempt_failure_le {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (hcodec : ∀ point, pointCodec point = none ↔ point = 0)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k) construct history vk pub).toOuterMeasure
        (plonkAttemptSuccessSet pointCodec scalarCodec)ᶜ ≤
      (((22 * actions + 45 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        ((148 * actions + 68 : ℕ) : ℝ≥0∞) * challenge255Bias := by
  calc
    _ ≤ ((((22 * actions + 2 * urs.k + 11 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (fieldSampleCount actions : ℕ) * challenge255Bias) +
          (widePlonkChallenges urs.k).toOuterMeasure {ch | PlonkFailureChallenges ch} :=
      freshPlonkAttempt_failure_le urs hk (widePlonkChallenges urs.k) construct history vk pub
        pointCodec scalarCodec hcodec hW
    _ ≤ ((((22 * actions + 2 * urs.k + 11 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (fieldSampleCount actions : ℕ) * challenge255Bias) +
          ((((urs.k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
            ((urs.k + 11 : ℕ) : ℝ≥0∞) * challenge255Bias) :=
      add_le_add le_rfl (widePlonkFailureChallenges_le urs.k)
    _ = _ := by
      simp only [hk, fieldSampleCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      ring

end Zcash.Snark.ZeroKnowledge
