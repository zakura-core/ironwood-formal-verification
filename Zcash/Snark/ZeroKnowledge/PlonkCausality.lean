import Zcash.Snark.ZeroKnowledge.PlonkOpeningCausality
import Zcash.Snark.ZeroKnowledge.PlonkIpaCausality

/-!
# Causality of the complete reference prover

Every stage of the actual full-tape computation uses only challenges already
received at that stage. The eleven-round adapter reads the same fixed-size
private tape for every verifier challenge record; a sampling-law equality
connects it to the existing reference prover. The final prefix theorem includes
encoding and the specified abort checks, without excluding exceptional values.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)

private theorem stage_left {actions k : ℕ} {G : Type*}
    (proof : ProofString (plonkProofShape actions k) Fp G) (i : Fin 11) :
    plonkStageMessages proof (Fin.castAdd k i) = plonkPreIpaStages proof i := by
  unfold plonkStageMessages
  exact Fin.addCases_left i

private theorem stage_right {actions k : ℕ} {G : Type*}
    (proof : ProofString (plonkProofShape actions k) Fp G) (i : Fin k) :
    plonkStageMessages proof (Fin.natAdd 11 i) =
      [.point (proof.ipaRounds i).1, .point (proof.ipaRounds i).2] := by
  unfold plonkStageMessages
  exact Fin.addCases_right i

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Every actual emitted stage depends only on its received challenge prefix and the fixed private tape. -/
theorem plonkVerifierProofFromTape_stage_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (j : Fin (11 + urs.k))
    (hprefix : ∀ i < j.val, plonkAttemptChallenge left i = plonkAttemptChallenge right i)
    (htape : TapeAgrees tape tape') :
    plonkStageMessages
        (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left tape) j =
      plonkStageMessages
        (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right tape') j := by
  let lp := plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left tape
  let rp := plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right tape'
  revert hprefix
  refine Fin.addCases ?_ ?_ j
  · intro i hprefix
    change ∀ r < i.val, plonkAttemptChallenge left r = plonkAttemptChallenge right r at hprefix
    suffices h : plonkPreIpaStages lp i = plonkPreIpaStages rp i from
      (stage_left lp i).trans (h.trans (stage_left rp i).symm)
    fin_cases i
    · change absorbPoints2 (F := Fp) lp.adviceCommitments = absorbPoints2 rp.adviceCommitments
      rw [plonkVerifierProofFromTape_advice_causal urs vk pub witness left right tape tape' htape]
    · change absorbLookupPermuted (F := Fp) lp.lookupPermutedInput lp.lookupPermutedTable =
        absorbLookupPermuted rp.lookupPermutedInput rp.lookupPermutedTable
      have h := plonkVerifierProofFromTape_lookup_causal urs vk pub witness left right tape tape'
        (hprefix 0 (by decide)) htape
      rw [h.1, h.2]
    · change ([] : List (TranscriptElt Fp G)) = []
      rfl
    · change absorbPoints2 (F := Fp) lp.permutationProduct ++ absorbPoints2 lp.lookupProduct ++
          [.point lp.vanishingRandom] =
        absorbPoints2 rp.permutationProduct ++ absorbPoints2 rp.lookupProduct ++ [.point rp.vanishingRandom]
      have h := plonkVerifierProofFromTape_products_causal urs vk pub witness left right tape tape'
        (hprefix 0 (by decide)) (hprefix 1 (by decide)) (hprefix 2 (by decide)) htape
      rw [h.1, h.2, plonkVerifierProofFromTape_linear_causal urs vk pub witness left right tape tape' htape]
    · change absorbPoints (F := Fp) lp.hPieces = absorbPoints rp.hPieces
      rw [plonkVerifierProofFromTape_quotient_causal urs vk pub witness left right tape tape'
        (hprefix 0 (by decide)) (hprefix 1 (by decide)) (hprefix 2 (by decide)) (hprefix 3 (by decide)) htape]
    · change plonkEvaluationStage lp = plonkEvaluationStage rp
      exact plonkVerifierProofFromTape_evaluations_causal urs vk pub witness left right tape tape'
        (hprefix 0 (by decide)) (hprefix 1 (by decide)) (hprefix 2 (by decide)) (hprefix 4 (by decide)) htape
    · change ([] : List (TranscriptElt Fp G)) = []
      rfl
    · change ([TranscriptElt.point lp.multiopenQPrime] : List (TranscriptElt Fp G)) =
        [TranscriptElt.point rp.multiopenQPrime]
      rw [plonkVerifierProofFromTape_qPrime_causal urs vk pub witness left right tape tape'
        (hprefix 0 (by decide)) (hprefix 1 (by decide)) (hprefix 2 (by decide)) (hprefix 3 (by decide))
        (hprefix 4 (by decide)) (hprefix 5 (by decide)) (hprefix 6 (by decide)) htape]
    · change absorbScalars (G := G) lp.multiopenU = absorbScalars rp.multiopenU
      rw [plonkVerifierProofFromTape_groupValues_causal urs vk pub witness left right tape tape'
        (hprefix 0 (by decide)) (hprefix 1 (by decide)) (hprefix 2 (by decide)) (hprefix 3 (by decide))
        (hprefix 4 (by decide)) (hprefix 5 (by decide)) (hprefix 7 (by decide)) htape]
    · change ([TranscriptElt.point lp.ipaS] : List (TranscriptElt Fp G)) = [TranscriptElt.point rp.ipaS]
      rw [plonkVerifierProofFromTape_mask_causal urs vk pub witness left right tape tape'
        (hprefix 7 (by decide)) htape]
    · change ([] : List (TranscriptElt Fp G)) = []
      rfl
  · intro i hprefix
    change ∀ r < 11 + i.val, plonkAttemptChallenge left r = plonkAttemptChallenge right r at hprefix
    have hrounds (r : Fin urs.k) (hr : r.val < i.val) : left.ipaRound r = right.ipaRound r := by
      simpa only [plonkAttemptChallenge_round] using
        hprefix (11 + r.val) (Nat.add_lt_add_left hr 11)
    have h := plonkVerifierProofFromTape_round_causal urs vk pub witness left right tape tape'
      (hprefix 0 (by omega)) (hprefix 1 (by omega)) (hprefix 2 (by omega)) (hprefix 3 (by omega))
      (hprefix 4 (by omega)) (hprefix 5 (by omega)) (hprefix 6 (by omega)) (hprefix 7 (by omega))
      (hprefix 8 (by omega)) (hprefix 9 (by omega)) (hprefix 10 (by omega)) i hrounds htape
    suffices hp : ([TranscriptElt.point (lp.ipaRounds i).1, .point (lp.ipaRounds i).2] :
        List (TranscriptElt Fp G)) = [.point (rp.ipaRounds i).1, .point (rp.ipaRounds i).2] from
      (stage_right lp i).trans (hp.trans (stage_right rp i).symm)
    rw [h]

/-- The specified eleven-round reference prover on one fixed `148m+46`-sample private tape. -/
def plonkReferenceProofFromTape {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges urs.k Fp)
    (tape : Fin (fieldSampleCount actions) → Fp) : ProofString (plonkProofShape actions urs.k) Fp G :=
  plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness ch) [] urs vk pub ch
    (tape ∘ Fin.cast (plonkJointSampleCount_eq (plonkTotalColumnConstructor vk pub witness ch) hk))

private theorem sampleFieldsWith_cast {A : Type*} {n m : ℕ} (h : n = m)
    (finish : (Fin n → Fp) → A) :
    sampleFieldsWith m (fun tape => finish (tape ∘ Fin.cast h)) = sampleFieldsWith n finish := by
  subst m
  rfl

/-- The fixed-tape adapter has exactly the existing reference prover's wide-reduced sampling law. -/
theorem plonkReferenceProofFromTape_law {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (ch : Challenges urs.k Fp) :
    (sampleFieldsWith (fieldSampleCount actions)
      (plonkReferenceProofFromTape urs hk vk pub witness ch)).runFreshPMF fieldSample =
        sampledPlonkVerifierProver (plonkTotalColumnConstructor vk pub witness ch) [] urs vk pub ch := by
  rw [sampledPlonkVerifierProver_fromTape]
  unfold plonkReferenceProofFromTape
  rw [sampleFieldsWith_cast]

/-- The entire reference-prover message schedule is causal on every fixed private tape. -/
theorem plonkReferenceProofFromTape_causal {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (tape : Fin (fieldSampleCount actions) → Fp) :
    ProtocolCausal plonkAttemptChallenge
      (fun ch => plonkAttemptTrace (plonkReferenceProofFromTape urs hk vk pub witness ch tape)) := by
  apply plonkAttemptTrace_causal_of_stages
  intro j left right hprefix
  dsimp only [plonkReferenceProofFromTape]
  apply plonkVerifierProofFromTape_stage_causal urs vk pub witness left right _ _ j hprefix
  intro i i' hii
  exact congrArg tape (Fin.ext hii)

/-- Encoding and the actual abort checks preserve the complete reference prover's causal prefixes. -/
theorem plonkReferenceProofFromTape_observation_causal {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (tape : Fin (fieldSampleCount actions) → Fp)
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (n : ℕ) (left right : Challenges urs.k Fp)
    (hprefix : ∀ i < n, plonkAttemptChallenge left i = plonkAttemptChallenge right i) :
    observeProtocolTrace pointCodec scalarCodec (plonkAttemptChallenge left) (plonkAfterChallenge left) 0
        (protocolPrefix n (plonkAttemptTrace (plonkReferenceProofFromTape urs hk vk pub witness left tape))) =
      observeProtocolTrace pointCodec scalarCodec (plonkAttemptChallenge right) (plonkAfterChallenge right) 0
        (protocolPrefix n (plonkAttemptTrace (plonkReferenceProofFromTape urs hk vk pub witness right tape))) :=
  plonkProtocolCausal_observation pointCodec scalarCodec
    (fun ch => plonkReferenceProofFromTape urs hk vk pub witness ch tape)
    (plonkReferenceProofFromTape_causal urs hk vk pub witness tape) n left right hprefix

end Zcash.Snark.ZeroKnowledge
