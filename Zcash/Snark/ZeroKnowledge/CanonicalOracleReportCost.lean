import Zcash.Snark.ZeroKnowledge.CanonicalObserverCost
import Zcash.Snark.ZeroKnowledge.ProtocolPrefixCost
import Zcash.Snark.ZeroKnowledge.ProtocolOracle

/-! # Complete cost of the original canonical oracle reports -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Count every visited transcript cell while counting its challenge markers. -/
def protocolChallengeCountCosted {F G : Type*} : List (TranscriptElt F G) → ℕ × ℕ
  | [] => (0, 1)
  | .challenge :: rest =>
    let tail := protocolChallengeCountCosted rest
    (1 + tail.1, tail.2 + 3)
  | .point _ :: rest | .scalar _ :: rest =>
    let tail := protocolChallengeCountCosted rest
    (tail.1, tail.2 + 2)

/-- The counted scan returns the original exact challenge count. -/
theorem protocolChallengeCountCosted_result {F G : Type*} (trace : List (TranscriptElt F G)) :
    (protocolChallengeCountCosted trace).1 = protocolChallengeCount trace := by
  induction trace with
  | nil => rfl
  | cons item rest ih => cases item <;> simp only [protocolChallengeCountCosted, protocolChallengeCount, ih]

/-- The complete marker count takes at most three operations per transcript cell. -/
theorem protocolChallengeCountCosted_cost_le {F G : Type*} (trace : List (TranscriptElt F G)) :
    (protocolChallengeCountCosted trace).2 ≤ 3 * trace.length + 1 := by
  induction trace with
  | nil => simp [protocolChallengeCountCosted]
  | cons item rest ih =>
    cases item <;> simp only [protocolChallengeCountCosted, List.length_cons] <;> omega

/-- Copy the due prefix and apply the complete canonical observer, retaining both costs. -/
def canonicalProtocolOracleReportCosted (equal read : ℕ) {k : ℕ}
    (ch : Challenges k (Fp × ℕ)) (trace : List (TranscriptElt Fp VestaG)) (index : ℕ) :
    ProverAttemptResult × ℕ :=
  let due := protocolPrefixCosted index trace
  let observed := canonicalProtocolObserverCosted equal read ch due.1
  (observed.1, due.2 + observed.2 + 2)

/-- The report preserves the original raw-reply observer whenever the supplied fields are its reductions. -/
theorem canonicalProtocolOracleReportCosted_result (equal read : ℕ) {k : ℕ}
    (ch : Challenges k (Fp × ℕ)) (digests : ℕ → Fin challengeDigestCard)
    (hraw : ∀ i, ((digests i).val : Fp) = plonkAttemptChallenge (Challenges.eraseCosts ch) i)
    (trace : List (TranscriptElt Fp VestaG)) (index : ℕ) :
    (canonicalProtocolOracleReportCosted equal read ch trace index).1 =
      protocolOracleReport plonkPointCodec digests (plonkAfterChallenge (Challenges.eraseCosts ch)) trace index := by
  have hagree : (fun i => ((digests i).val : Fp)) = plonkAttemptChallenge (Challenges.eraseCosts ch) :=
    funext hraw
  simp only [canonicalProtocolOracleReportCosted, canonicalProtocolObserverCosted_result,
    protocolPrefixCosted_result, protocolOracleReport, hagree]

/-- Prefix copying, challenge materialization, encoding, and stopping checks are all included. -/
theorem canonicalProtocolOracleReportCosted_cost_le (equal read : ℕ) {k : ℕ}
    (ch : Challenges k (Fp × ℕ)) (trace : List (TranscriptElt Fp VestaG)) (index access : ℕ)
    (hread : Challenges.ReadBound ch access) :
    (canonicalProtocolOracleReportCosted equal read ch trace index).2 ≤
      (11 + k) * (access + 2) + k * k + 15 +
        trace.length * (access + 4 * k + 2 * read + 3 * equal + 3600) + 4 * trace.length + 7 := by
  have hp := protocolPrefixCosted_cost_le index trace
  have hl := protocolPrefixCosted_length_le index trace
  have ho := canonicalProtocolObserverCosted_cost_le equal read ch
    (protocolPrefixCosted index trace).1 access hread
  have hm := Nat.mul_le_mul_right (access + 4 * k + 2 * read + 3 * equal + 3600) hl
  dsimp only [canonicalProtocolOracleReportCosted]
  omega

end Zcash.Snark.ZeroKnowledge
