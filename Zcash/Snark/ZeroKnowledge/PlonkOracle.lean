import Zcash.Snark.ZeroKnowledge.RawChallenges
import Zcash.Snark.ZeroKnowledge.ProtocolOracle
import Zcash.Snark.ZeroKnowledge.PlonkCausality

/-!
# The actual PLONK and IPA reference prover as an oracle computation

The online driver uses the existing full private-tape prover, canonical proof
codecs, and actual post-challenge checks. Its checked causality supplies every
prefix dependency. Independent raw replies replay exactly the original typed
proof and observed attempt, including exceptional challenges and early stops.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Common

/-- The actual attempt observation with its raw query/response prefix. -/
def plonkRawOracleView {actions k : ℕ} (initial : List (TranscriptElt Fp VestaG))
    (digests : PlonkChallengeTape k (Fin challengeDigestCard))
    (proof : ProofString (plonkProofShape actions k) Fp VestaG) :
    ProverAttemptResult × List (TranscriptHashAddress × Fin challengeDigestCard) :=
  protocolOracleView plonkPointCodec initial (extendDigestTape digests)
    (plonkAfterChallenge (plonkChallengesFromDigests k (extendDigestTape digests))) (plonkAttemptTrace proof)

/-- The oracle view retains exactly the original canonical attempt result. -/
theorem plonkRawOracleView_result {actions k : ℕ} (initial : List (TranscriptElt Fp VestaG))
    (digests : PlonkChallengeTape k (Fin challengeDigestCard))
    (proof : ProofString (plonkProofShape actions k) Fp VestaG) :
    (plonkRawOracleView initial digests proof).1 =
      observePlonkAttempt plonkPointCodec plonkScalarCodec
        (plonkChallengesFromTape (fun i => ((digests i).val : Fp)), proof) := by
  unfold plonkRawOracleView observePlonkAttempt
  rw [protocolOracleView_result, ← plonkChallengesFromDigests_extend]
  have hread : (fun i => ((extendDigestTape digests i).val : Fp)) =
      plonkAttemptChallenge (plonkChallengesFromDigests k (extendDigestTape digests)) :=
    funext fun i => (plonkChallengesFromDigests_extend_read digests i).symm
  rw [hread]

/-- Every challenge of a completed canonical proof appears in its recorded raw-oracle trace. -/
theorem plonkRawOracleView_query_mem_of_complete {actions k : ℕ}
    (initial : List (TranscriptElt Fp VestaG))
    (digests : PlonkChallengeTape k (Fin challengeDigestCard))
    (proof : ProofString (plonkProofShape actions k) Fp VestaG)
    (hcomplete : (observePlonkAttempt plonkPointCodec plonkScalarCodec
      (plonkChallengesFromTape (fun i => ((digests i).val : Fp)), proof)).status = .complete)
    (i : Fin (k + 11)) :
    (protocolQueryAddress initial (plonkAttemptTrace proof) i.val, digests i) ∈
      (plonkRawOracleView initial digests proof).2 := by
  have hcontinued : protocolAttemptContinues (plonkRawOracleView initial digests proof).1 = true := by
    rw [plonkRawOracleView_result]
    change decide ((observePlonkAttempt plonkPointCodec plonkScalarCodec
      (plonkChallengesFromTape (fun i => ((digests i).val : Fp)), proof)).status = .complete) = true
    exact decide_eq_true hcomplete
  have hqueries := replayOracleSchedule_queries_of_complete
    (protocolOracleReport plonkPointCodec (extendDigestTape digests)
      (plonkAfterChallenge (plonkChallengesFromDigests k (extendDigestTape digests)))
      (plonkAttemptTrace proof))
    protocolAttemptContinues (protocolQueryAddress initial (plonkAttemptTrace proof))
    (extendDigestTape digests) (protocolChallengeCount (plonkAttemptTrace proof)) 0 hcontinued
  change (protocolQueryAddress initial (plonkAttemptTrace proof) i.val, digests i) ∈
    (replayOracleSchedule _ _ _ _ _ _).2
  rw [hqueries]
  apply List.mem_map.mpr
  refine ⟨i.val, ?_, ?_⟩
  · apply List.mem_range'_1.mpr
    constructor
    · exact Nat.zero_le _
    · rw [plonkAttemptTrace_challengeCount]
      have hi := i.isLt
      omega
  · simp only [extendDigestTape_fin]

/-- Internal query collisions are impossible even on an exceptional or incomplete attempt. -/
theorem plonkRawOracleView_queries_nodup {actions k : ℕ} (initial : List (TranscriptElt Fp VestaG))
    (digests : PlonkChallengeTape k (Fin challengeDigestCard))
    (proof : ProofString (plonkProofShape actions k) Fp VestaG) :
    ((plonkRawOracleView initial digests proof).2.map Prod.fst).Nodup :=
  protocolOracleView_queries_nodup _ _ _ _ _

variable [Module Fp VestaG]

/-- The same complete reference message schedule, with its field challenges read from raw digests. -/
def plonkReferenceOracleTrace {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (privateTape : Fin (fieldSampleCount actions) → Fp)
    (digests : ℕ → Fin challengeDigestCard) : List (TranscriptElt Fp VestaG) :=
  plonkAttemptTrace (plonkReferenceProofFromTape urs hk vk pub witness
    (plonkChallengesFromDigests urs.k digests) privateTape)

/-- The original full-tape causality theorem supplies every raw-oracle prefix dependency. -/
theorem plonkReferenceOracleTrace_causal {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (privateTape : Fin (fieldSampleCount actions) → Fp) :
    ProtocolCausal (fun raw i => ((raw i).val : Fp))
      (plonkReferenceOracleTrace urs hk vk pub witness privateTape) := by
  intro n left right hprefix
  exact plonkReferenceProofFromTape_causal urs hk vk pub witness privateTape n
    (plonkChallengesFromDigests urs.k left) (plonkChallengesFromDigests urs.k right)
    (plonkChallengesFromDigests_prefix urs.k n left right hprefix)

/-- Execute the reference attempt against raw hash queries, with all specified abort checks. -/
def plonkReferenceOracleComp {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (privateTape : Fin (fieldSampleCount actions) → Fp)
    (initial : List (TranscriptElt Fp VestaG)) :
    OracleComp TranscriptHashAddress (Fin challengeDigestCard) ProverAttemptResult :=
  protocolOracleComp plonkPointCodec initial (plonkReferenceOracleTrace urs hk vk pub witness privateTape)
    (fun raw => plonkAfterChallenge (plonkChallengesFromDigests urs.k raw)) (urs.k + 11)

/-- The concrete eleven-round attempt has at most twenty-two raw oracle queries. -/
theorem plonkReferenceOracleComp_queryBound {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (privateTape : Fin (fieldSampleCount actions) → Fp)
    (initial : List (TranscriptElt Fp VestaG)) :
    (plonkReferenceOracleComp urs hk vk pub witness privateTape initial).QueryBound (urs.k + 11) :=
  protocolOracleComp_queryBound _ _ _ _ _

/-- One full raw tape replays the same reference proof and exact query/response history. -/
theorem plonkReferenceOracleComp_replay {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp VestaG) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (privateTape : Fin (fieldSampleCount actions) → Fp)
    (initial : List (TranscriptElt Fp VestaG)) (digests : PlonkChallengeTape urs.k (Fin challengeDigestCard)) :
    freshOracleRunTape (urs.k + 11) (plonkReferenceOracleComp urs hk vk pub witness privateTape initial) digests =
      some (plonkRawOracleView initial digests (plonkReferenceProofFromTape urs hk vk pub witness
        (plonkChallengesFromTape (fun i => ((digests i).val : Fp))) privateTape)) := by
  have hcount (raw : ℕ → Fin challengeDigestCard) :
      protocolChallengeCount (plonkReferenceOracleTrace urs hk vk pub witness privateTape raw) = urs.k + 11 := by
    rw [plonkReferenceOracleTrace, plonkAttemptTrace_challengeCount, Nat.add_comm]
  have h := protocolOracleComp_replay plonkPointCodec initial
    (plonkReferenceOracleTrace urs hk vk pub witness privateTape)
    (fun raw => plonkAfterChallenge (plonkChallengesFromDigests urs.k raw))
    (plonkReferenceOracleTrace_causal urs hk vk pub witness privateTape) (plonkAfterDigests_causal urs.k)
    (urs.k + 11) hcount (extendDigestTape digests)
  simpa only [plonkReferenceOracleComp, plonkRawOracleView, plonkReferenceOracleTrace,
    extendDigestTape_fin, plonkChallengesFromDigests_extend] using h

end Zcash.Snark.ZeroKnowledge
