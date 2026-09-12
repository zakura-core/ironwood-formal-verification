import Zcash.Snark.ZeroKnowledge.OracleProgrammingCost
import Zcash.Snark.ZeroKnowledge.OracleTableResources
import Zcash.Snark.ZeroKnowledge.PlonkOracle
import Zcash.Snark.ZeroKnowledge.PlonkTranscriptSize

/-!
# Cache-phase costs for the existing protocol view

These bounds apply the costed byte-cache algorithm to the actual oracle log,
including all stopped prefixes. They bound this phase after constructing the
view; the arithmetic, serialization, and observer costs of that construction
are separate. No success, nonzero-challenge, or well-formed-proof premise is used.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The original receive count and serialized prefix sizes bound protocol-view programming. -/
theorem protocolOracleView_programming_cost_le
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (pointCodec : VestaG → Option (List UInt8))
    (initial : List (TranscriptElt Fp VestaG)) (digests : ℕ → Fin challengeDigestCard)
    (check : ℕ → Option ProverAttemptFailure) (trace : List (TranscriptElt Fp VestaG)) :
    (programOracleViewCosted cache (protocolOracleView pointCodec initial digests check trace)).2 ≤
      protocolChallengeCount trace * ((cache.length + protocolChallengeCount trace) *
        (2 * (16 + 65 * (initial.length + trace.length + 1)) + 5) + 4) + 2 :=
  programOracleViewCosted_cost_le cache _ _ _
    (protocolOracleView_queries_length_le pointCodec initial trace digests check)
    (protocolOracleView_query_bytes_le pointCodec initial digests check trace)

/-- For PLONK and IPA the cache phase is polynomial in public prefix size, Actions, and rounds. -/
theorem plonkRawOracleView_programming_cost_le {actions k : ℕ}
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (initial : List (TranscriptElt Fp VestaG))
    (digests : PlonkChallengeTape k (Fin challengeDigestCard))
    (proof : ProofString (plonkProofShape actions k) Fp VestaG) :
    (programOracleViewCosted cache (plonkRawOracleView initial digests proof)).2 ≤
      (11 + k) * ((cache.length + (11 + k)) *
        (2 * (16 + 65 * (initial.length + 72 * actions + 3 * k + 75)) + 5) + 4) + 2 := by
  apply programOracleViewCosted_cost_le
  · have h := protocolOracleView_queries_length_le plonkPointCodec initial
      (plonkAttemptTrace proof) (extendDigestTape digests)
      (plonkAfterChallenge (plonkChallengesFromDigests k (extendDigestTape digests)))
    simpa only [plonkAttemptTrace_challengeCount] using h
  · intro entry hentry
    have h := protocolOracleView_query_bytes_le plonkPointCodec initial (extendDigestTape digests)
      (plonkAfterChallenge (plonkChallengesFromDigests k (extendDigestTape digests)))
      (plonkAttemptTrace proof) entry hentry
    have hsize := plonkAttemptTrace_length_le proof
    omega

end Zcash.Snark.ZeroKnowledge
