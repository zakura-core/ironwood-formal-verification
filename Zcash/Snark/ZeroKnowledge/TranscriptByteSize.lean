import Zcash.Snark.ZeroKnowledge.ProtocolOracle

/-!
# Byte-size bounds for actual oracle queries

The transcript's point, scalar, and challenge encodings have bounded widths.
Every query is a serialized prefix of the supplied initial transcript and proof
schedule, with one additional challenge marker. The bounds include the separate
sixteen-byte personalization. They apply to unsuccessful attempts as well.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The largest tagged transcript element is a point with two 32-byte coordinates. -/
theorem transcriptElementBytes_length_le (element : TranscriptElt Fp VestaG) :
    (transcriptElementBytes element).length ≤ 65 := by
  cases element <;>
    simp [transcriptElementBytes, vestaAffineCodec_length, plonkScalarCodec_length]

/-- Serialization has a linear size bound in the number of typed transcript elements. -/
theorem transcriptBytes_length_le (elements : List (TranscriptElt Fp VestaG)) :
    (transcriptBytes elements).length ≤ 65 * elements.length := by
  induction elements with
  | nil => simp [transcriptBytes]
  | cons element rest ih =>
    have h := transcriptElementBytes_length_le element
    simp only [transcriptBytes, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

/-- A receive address contains at most the initial transcript, the full schedule, and one marker. -/
theorem protocolQueryPrefix_length_le {F G : Type*}
    (initial trace : List (TranscriptElt F G)) (index : ℕ) :
    (protocolQueryPrefix initial trace index).length ≤ initial.length + trace.length + 1 := by
  have h := (protocolPrefix_isPrefix index trace).length_le
  simp only [protocolQueryPrefix, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Include both byte-list components of every address queried by the protocol. -/
theorem protocolQueryAddress_bytes_le (initial trace : List (TranscriptElt Fp VestaG)) (index : ℕ) :
    (protocolQueryAddress initial trace index).1.length +
      (protocolQueryAddress initial trace index).2.length ≤
      16 + 65 * (initial.length + trace.length + 1) := by
  have h := (transcriptBytes_length_le (protocolQueryPrefix initial trace index)).trans
    (Nat.mul_le_mul_left 65 (protocolQueryPrefix_length_le initial trace index))
  change halo2TranscriptPersonalization.length +
    (transcriptBytes (protocolQueryPrefix initial trace index)).length ≤ _
  rw [halo2TranscriptPersonalization_length]
  omega

/-- Every entry of the actual retained oracle log satisfies the same public size envelope. -/
theorem protocolOracleView_query_bytes_le (pointCodec : VestaG → Option (List UInt8))
    (initial : List (TranscriptElt Fp VestaG)) (digests : ℕ → Fin challengeDigestCard)
    (check : ℕ → Option ProverAttemptFailure) (trace : List (TranscriptElt Fp VestaG))
    (entry : TranscriptHashAddress × Fin challengeDigestCard)
    (hentry : entry ∈ (protocolOracleView pointCodec initial digests check trace).2) :
    entry.1.1.length + entry.1.2.length ≤ 16 + 65 * (initial.length + trace.length + 1) := by
  have hprefix := replayOracleSchedule_queries_prefix
    (protocolOracleReport pointCodec digests check trace) protocolAttemptContinues
    (protocolQueryAddress initial trace) digests (protocolChallengeCount trace) 0
  obtain ⟨i, _, hi⟩ := List.mem_map.mp (hprefix.subset hentry)
  rw [← hi]
  exact protocolQueryAddress_bytes_le initial trace i

end Zcash.Snark.ZeroKnowledge
