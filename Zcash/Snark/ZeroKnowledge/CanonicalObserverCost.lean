import Zcash.Snark.ZeroKnowledge.ProtocolObserverCost
import Zcash.Snark.ZeroKnowledge.ChallengeScheduleCost
import Zcash.Snark.ZeroKnowledge.PointEncodingCost

/-! # Complete original attempt observation with the canonical codecs and checks -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Materialize the challenge schedule and run the original canonical observer with complete costs. -/
def canonicalProtocolObserverCosted (equal read : ℕ) {k : ℕ}
    (ch : Challenges k (Fp × ℕ)) (trace : List (TranscriptElt Fp VestaG)) : ProverAttemptResult × ℕ :=
  let sequence := plonkChallengeSequenceCosted ch
  let observed := observeProtocolTraceCosted
    (fun point => plonkPointCodecCosted equal (point, 1))
    (fun scalar => plonkScalarCodecCosted (scalar, 1))
    (getDListCosted read (0 : Fp) sequence.1)
    (afterStoredChallengeCosted equal read ch.x sequence.1) 0 trace
  (observed.1, sequence.2 + observed.2 + 2)

/-- Canonical bytes, received values, and every original abort branch are preserved. -/
theorem canonicalProtocolObserverCosted_result (equal read : ℕ) {k : ℕ}
    (ch : Challenges k (Fp × ℕ)) (trace : List (TranscriptElt Fp VestaG)) :
    (canonicalProtocolObserverCosted equal read ch trace).1 =
      observeProtocolTrace plonkPointCodec plonkScalarCodec
        (plonkAttemptChallenge (Challenges.eraseCosts ch))
        (plonkAfterChallenge (Challenges.eraseCosts ch)) 0 trace := by
  simp only [canonicalProtocolObserverCosted, observeProtocolTraceCosted_result,
    plonkPointCodecCosted_result, plonkScalarCodecCosted_result,
    plonkChallengeSequenceCosted_result, afterStoredChallengeCosted_result,
    getDListCosted_result]
  rfl

/-- A complete bound includes challenge preparation, actual codecs, received values, and failure checks. -/
theorem canonicalProtocolObserverCosted_cost_le (equal read : ℕ) {k : ℕ}
    (ch : Challenges k (Fp × ℕ)) (trace : List (TranscriptElt Fp VestaG))
    (access : ℕ) (hread : Challenges.ReadBound ch access) :
    (canonicalProtocolObserverCosted equal read ch trace).2 ≤
      (11 + k) * (access + 2) + k * k + 15 +
        trace.length * (access + 4 * k + 2 * read + 3 * equal + 3600) + 3 := by
  let sequence := plonkChallengeSequenceCosted ch
  have hseq := plonkChallengeSequenceCosted_cost_le ch access hread
  have hlen : sequence.1.length = 11 + k := plonkChallengeSequenceCosted_length ch
  have hx := hread.2.2.2.2.1
  have hpoint (point : VestaG) : (plonkPointCodecCosted equal (point, 1)).2 ≤ 3492 + equal := by
    have h := plonkPointCodecCosted_cost_le equal (point, 1)
    omega
  have hwidth (point : VestaG) (bytes : List UInt8)
      (hbytes : bytes ∈ (plonkPointCodecCosted equal (point, 1)).1) : bytes.length ≤ 32 := by
    have hencoded : plonkPointCodec point = some bytes := by
      simpa only [plonkPointCodecCosted_result, Option.mem_def] using hbytes
    exact le_of_eq (plonkPointCodec_length point bytes hencoded)
  have hscalar (scalar : Fp) : (plonkScalarCodecCosted (scalar, 1)).2 ≤ 3492 + equal := by
    have h := plonkScalarCodecCosted_cost_le (scalar, 1)
    omega
  have hscalarWidth (scalar : Fp) : (plonkScalarCodecCosted (scalar, 1)).1.length ≤ 32 := by
    rw [plonkScalarCodecCosted_result, plonkScalarCodec_length]
  have hchallenge (index : ℕ) : (getDListCosted read (0 : Fp) sequence.1 index).2 ≤ 2 * (11 + k) + read + 1 := by
    have h := getDListCosted_cost_le read (0 : Fp) sequence.1 index
    rwa [hlen] at h
  have hcheck (index : ℕ) : (afterStoredChallengeCosted equal read ch.x sequence.1 index).2 ≤
      access + 2 * (11 + k) + read + 2 * equal + 11 := by
    have h := afterStoredChallengeCosted_cost_le equal read ch.x sequence.1 index
    rw [hlen] at h
    omega
  have hobs := observeProtocolTraceCosted_cost_le
    (fun point => plonkPointCodecCosted equal (point, 1))
    (fun scalar => plonkScalarCodecCosted (scalar, 1))
    (getDListCosted read (0 : Fp) sequence.1)
    (afterStoredChallengeCosted equal read ch.x sequence.1)
    (3492 + equal) 32 (2 * (11 + k) + read + 1)
    (access + 2 * (11 + k) + read + 2 * equal + 11)
    hpoint hwidth hscalar hscalarWidth hchallenge hcheck 0 trace
  dsimp only [canonicalProtocolObserverCosted]
  nlinarith only [hseq, hobs]

end Zcash.Snark.ZeroKnowledge
