import Zcash.Snark.ZeroKnowledge.TranscriptBytes
import Zcash.Snark.ZeroKnowledge.Randomness

/-!
# A raw-digest oracle at the existing Fiat–Shamir boundary

An address records the BLAKE2b personalization and the absorbed bytes. Oracle
responses are raw 512-bit integers, reduced only when returned to the existing
typed verifier. This defines the byte/hash boundary; it does not itself prove
random-oracle security or identify concrete BLAKE2b with an ideal oracle.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The personalization and message supplied to the raw hash oracle. -/
abbrev TranscriptHashAddress := List UInt8 × List UInt8

/-- Encode exactly the typed absorb prefix under the specified hash domain. -/
def transcriptHashAddress (absorbed : List (TranscriptElt Fp VestaG)) : TranscriptHashAddress :=
  (halo2TranscriptPersonalization, transcriptBytes absorbed)

/-- The byte/hash boundary introduces no collisions between typed transcript prefixes. -/
theorem transcriptHashAddress_injective : Function.Injective transcriptHashAddress := by
  intro left right h
  exact transcriptBytes_injective (congrArg Prod.snd h)

/-- A squeeze appends just the challenge marker to the running transcript. -/
theorem transcriptHashAddress_squeeze (absorbed : List (TranscriptElt Fp VestaG)) :
    transcriptHashAddress (absorbed ++ [.challenge]) =
      (halo2TranscriptPersonalization, transcriptBytes absorbed ++ [0x00]) := by
  simp [transcriptHashAddress, transcriptBytes, transcriptElementBytes]

/-- Every squeeze strictly extends its byte prefix, even when no message precedes it. -/
theorem transcriptBytes_squeeze_length (absorbed : List (TranscriptElt Fp VestaG)) :
    (transcriptBytes (absorbed ++ [.challenge])).length = (transcriptBytes absorbed).length + 1 := by
  simp only [transcriptBytes_append, List.length_append]
  rfl

/-- Reduce the digest's little-endian integer modulo `p`.
For digest bytes `b₀, …, b₆₃`, the supplied hash value is `∑ᵢ bᵢ · 256ⁱ`, matching
pinned Common's `Challenge255::new` and Pasta `Fp::from_uniform_bytes`. -/
def byteFiatShamir (hash : TranscriptHashAddress → Fin challengeDigestCard) : FiatShamir Fp VestaG where
  squeeze absorbed := ((hash (transcriptHashAddress absorbed)).val : Fp)

/-- The challenge boundary performs exactly digest-to-field reduction. -/
theorem byteFiatShamir_squeeze (hash : TranscriptHashAddress → Fin challengeDigestCard)
    (absorbed : List (TranscriptElt Fp VestaG)) :
    (byteFiatShamir hash).squeeze absorbed = ((hash (transcriptHashAddress absorbed)).val : Fp) := rfl

/-- The first query includes the public key representation, configured instances, and advice commitments. -/
theorem byteFiatShamir_statement_theta {shape : Shape}
    (hash : TranscriptHashAddress → Fin challengeDigestCard) (vkTranscriptRepr : Fp)
    (instances : Fin shape.numProofs → ℕ → VestaG) (proof : ProofString shape Fp VestaG) :
    (deriveChallengesForStatement (byteFiatShamir hash) vkTranscriptRepr instances proof).theta =
      ((hash (transcriptHashAddress
        (initialTranscript vkTranscriptRepr instances ++ absorbPoints2 proof.adviceCommitments ++ [.challenge]))).val : Fp) :=
  rfl

end Zcash.Snark.ZeroKnowledge
