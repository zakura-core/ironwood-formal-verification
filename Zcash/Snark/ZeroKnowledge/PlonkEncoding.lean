import Zcash.Snark.ZeroKnowledge.ProofEncoding
import Zcash.Snark.ZeroKnowledge.ProofSize
import Zcash.Snark.ZeroKnowledge.PlonkCausality

/-!
# The full reference attempt with the specified byte encodings

This observer uses the canonical scalar and compressed Vesta encodings from the
pinned description. It retains the verifier tape, received challenges, failure
status, and emitted prefix. Its complete output has the prescribed proof size;
the same observer also preserves the checked reference prover's causal prefixes.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Common

/-- The entire observable attempt with the specified encodings and existing abort policy. -/
def encodedPlonkAttempt {actions k : ℕ} (view : PlonkFreshView actions k VestaG) :
    Challenges k Fp × ProverAttemptResult :=
  plonkAttemptObservation plonkPointCodec plonkScalarCodec view

/-- The canonical point encoder gives exactly the already specified completion conditions. -/
theorem encodedPlonkAttempt_complete_iff {actions k : ℕ}
    (view : PlonkFreshView actions k VestaG) :
    (encodedPlonkAttempt view).2.status = .complete ↔
      (TranscriptElt.point 0 ∉ plonkAttemptTrace view.2) ∧
        view.1.x ≠ 0 ∧ ∀ j, view.1.ipaRound j ≠ 0 := by
  change (observePlonkAttempt plonkPointCodec plonkScalarCodec view).status = .complete ↔ _
  rw [plonkAttempt_complete_iff plonkPointCodec plonkScalarCodec plonkPointCodec_none_iff]
  constructor
  · intro h
    exact ⟨fun hzero => h.1 0 hzero rfl, h.2⟩
  · intro h
    exact ⟨fun point hmem hzero => h.1 (hzero ▸ hmem), h.2⟩

variable [Module Fp VestaG]

/-- Run the actual eleven-round reference prover and encode its observed attempt. -/
def plonkReferenceAttemptFromTape {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges urs.k Fp) (tape : Fin (fieldSampleCount actions) → Fp) :
    Challenges urs.k Fp × ProverAttemptResult :=
  encodedPlonkAttempt (ch, plonkReferenceProofFromTape urs hk vk pub witness ch tape)

/-- Sampling the fixed-tape byte observer gives the existing reference law followed by that same observer. -/
theorem plonkReferenceAttemptFromTape_law {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges urs.k Fp) :
    (sampleFieldsWith (fieldSampleCount actions)
      (plonkReferenceAttemptFromTape urs hk vk pub witness ch)).runFreshPMF fieldSample =
      (sampledPlonkVerifierProver (plonkTotalColumnConstructor vk pub witness ch) [] urs vk pub ch).map
        (fun proof => encodedPlonkAttempt (ch, proof)) := by
  rw [← plonkReferenceProofFromTape_law urs hk vk pub witness ch]
  simpa only [plonkReferenceAttemptFromTape, Function.comp_def] using
    (sampleFieldsWith_map (fieldSampleCount actions)
      (plonkReferenceProofFromTape urs hk vk pub witness ch)
      (fun proof => encodedPlonkAttempt (ch, proof)) fieldSample)

/-- Run the fixed-tape reference observer on independent wide-reduced private and verifier tapes. -/
noncomputable def freshEncodedPlonkReferenceAttempt {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    PMF (Challenges urs.k Fp × ProverAttemptResult) :=
  (widePlonkChallenges urs.k).bind fun ch =>
    (sampleFieldsWith (fieldSampleCount actions)
      (plonkReferenceAttemptFromTape urs hk vk pub witness ch)).runFreshPMF fieldSample

/-- The encoded tape experiment is exactly the existing fresh reference law under the canonical observer. -/
theorem freshEncodedPlonkReferenceAttempt_law [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    freshEncodedPlonkReferenceAttempt urs hk vk pub witness =
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub).map encodedPlonkAttempt := by
  unfold freshEncodedPlonkReferenceAttempt freshSampledPlonkVerifierProver
  rw [PMF.map_bind]
  congr 1
  funext ch
  rw [plonkReferenceAttemptFromTape_law, PMF.map_comp]
  rfl

/-- The existing reference construction emits exactly the pinned number of proof items. -/
theorem plonkReferenceProofFromTape_messageCount {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges urs.k Fp) (tape : Fin (fieldSampleCount actions) → Fp) :
    protocolMessageCount (plonkAttemptTrace (plonkReferenceProofFromTape urs hk vk pub witness ch tape)) =
      85 + 71 * actions := by
  unfold plonkReferenceProofFromTape plonkVerifierProofFromTape
  rw [plonkProofFromJointView_messageCount, hk]
  omega

/-- Every completed reference attempt has exactly `2720+2272m` bytes, with no separate trailer. -/
theorem plonkReferenceAttemptFromTape_proof_length {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges urs.k Fp) (tape : Fin (fieldSampleCount actions) → Fp)
    (hcomplete : (plonkReferenceAttemptFromTape urs hk vk pub witness ch tape).2.status = .complete) :
    (plonkReferenceAttemptFromTape urs hk vk pub witness ch tape).2.proof.length = 2720 + 2272 * actions := by
  have h := observeProtocolTrace_proof_length plonkPointCodec plonkScalarCodec
    (plonkAttemptChallenge ch) (plonkAfterChallenge ch) 32 0
    (plonkAttemptTrace (plonkReferenceProofFromTape urs hk vk pub witness ch tape))
    plonkPointCodec_length plonkScalarCodec_length hcomplete
  rw [plonkReferenceProofFromTape_messageCount urs hk vk pub witness ch tape] at h
  dsimp only [plonkReferenceAttemptFromTape, encodedPlonkAttempt,
    plonkAttemptObservation, observePlonkAttempt]
  exact h.trans (by ring)

/-- The specified byte encodings and failures preserve causality of every complete-prover prefix. -/
theorem plonkReferenceAttemptFromTape_prefix_causal {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (tape : Fin (fieldSampleCount actions) → Fp) (n : ℕ) (left right : Challenges urs.k Fp)
    (hprefix : ∀ i < n, plonkAttemptChallenge left i = plonkAttemptChallenge right i) :
    observeProtocolTrace plonkPointCodec plonkScalarCodec (plonkAttemptChallenge left) (plonkAfterChallenge left) 0
        (protocolPrefix n (plonkAttemptTrace (plonkReferenceProofFromTape urs hk vk pub witness left tape))) =
      observeProtocolTrace plonkPointCodec plonkScalarCodec (plonkAttemptChallenge right) (plonkAfterChallenge right) 0
        (protocolPrefix n (plonkAttemptTrace (plonkReferenceProofFromTape urs hk vk pub witness right tape))) :=
  plonkReferenceProofFromTape_observation_causal urs hk vk pub witness tape
    plonkPointCodec plonkScalarCodec n left right hprefix

end Zcash.Snark.ZeroKnowledge
