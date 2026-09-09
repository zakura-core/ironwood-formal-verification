import Zcash.Snark.ZeroKnowledge.CanonicalOracleReportCost
import Zcash.Snark.ZeroKnowledge.QueryAddressCost
import Zcash.Snark.ZeroKnowledge.OracleReplayCost

/-! # Complete canonical query production and stopping replay -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Construct reports and byte addresses, read raw replies, and execute every original stopping branch. -/
def canonicalProtocolOracleViewCosted (equal read : ℕ) {k : ℕ}
    (initial : List (TranscriptElt Fp VestaG)) (ch : Challenges k (Fp × ℕ))
    (digests : ℕ → Fin challengeDigestCard × ℕ) (trace : List (TranscriptElt Fp VestaG)) :
    (ProverAttemptResult × List (TranscriptHashAddress × Fin challengeDigestCard)) × ℕ :=
  let count := protocolChallengeCountCosted trace
  let replay := replayOracleScheduleCosted
    (canonicalProtocolOracleReportCosted equal read ch trace)
    (fun result => (protocolAttemptContinues result, 4))
    (protocolQueryAddressCosted read initial trace) digests count.1 0
  (replay.1, count.2 + replay.2 + 3)

/-- Cost erasure preserves the original canonical result and every retained raw query/reply pair. -/
theorem canonicalProtocolOracleViewCosted_result (equal read : ℕ) {k : ℕ}
    (initial : List (TranscriptElt Fp VestaG)) (ch : Challenges k (Fp × ℕ))
    (digests : ℕ → Fin challengeDigestCard × ℕ)
    (hraw : ∀ i, (((digests i).1).val : Fp) = plonkAttemptChallenge (Challenges.eraseCosts ch) i)
    (trace : List (TranscriptElt Fp VestaG)) :
    (canonicalProtocolOracleViewCosted equal read initial ch digests trace).1 =
      protocolOracleView plonkPointCodec initial (fun i => (digests i).1)
        (plonkAfterChallenge (Challenges.eraseCosts ch)) trace := by
  simp only [canonicalProtocolOracleViewCosted, replayOracleScheduleCosted_result,
    canonicalProtocolOracleReportCosted_result equal read ch (fun i => (digests i).1) hraw,
    protocolQueryAddressCosted_result, protocolChallengeCountCosted_result, protocolOracleView]

/-- A concrete envelope for the complete observed replay, including every prefix reconstruction. -/
def canonicalProtocolOracleViewBudget (equal read rounds initialLength traceLength challenges access replyRead : ℕ) : ℕ :=
  let report := (11 + rounds) * (access + 2) + rounds * rounds + 15 +
    traceLength * (access + 4 * rounds + 2 * read + 3 * equal + 3600) + 4 * traceLength + 7
  let query := 2 * initialLength + 5 * traceLength +
    (initialLength + traceLength + 1) * (64 * (read + 71) + 2154) + 30
  (challenges + 1) * (report + query + replyRead + 14) + 3 * traceLength + 8

/-- The complete replay bound retains supplied raw-reader costs and counts all generated data. -/
theorem canonicalProtocolOracleViewCosted_cost_le (equal read : ℕ) {k : ℕ}
    (initial : List (TranscriptElt Fp VestaG)) (ch : Challenges k (Fp × ℕ))
    (digests : ℕ → Fin challengeDigestCard × ℕ) (trace : List (TranscriptElt Fp VestaG))
    (access replyRead : ℕ) (hread : Challenges.ReadBound ch access)
    (hreply : ∀ i, (digests i).2 ≤ replyRead) :
    (canonicalProtocolOracleViewCosted equal read initial ch digests trace).2 ≤
      canonicalProtocolOracleViewBudget equal read k initial.length trace.length
        (protocolChallengeCount trace) access replyRead := by
  have hc := protocolChallengeCountCosted_cost_le trace
  have hr := replayOracleScheduleCosted_cost_le
    (canonicalProtocolOracleReportCosted equal read ch trace)
    (fun result => (protocolAttemptContinues result, 4))
    (protocolQueryAddressCosted read initial trace) digests
    ((11 + k) * (access + 2) + k * k + 15 +
      trace.length * (access + 4 * k + 2 * read + 3 * equal + 3600) + 4 * trace.length + 7)
    4 (2 * initial.length + 5 * trace.length +
      (initial.length + trace.length + 1) * (64 * (read + 71) + 2154) + 30) replyRead
    (fun index => canonicalProtocolOracleReportCosted_cost_le equal read ch trace index access hread)
    (fun _ => le_rfl) (fun index => protocolQueryAddressCosted_cost_le read initial trace index)
    hreply (protocolChallengeCountCosted trace).1 0
  conv at hr =>
    rhs
    rw [protocolChallengeCountCosted_result]
  dsimp only [canonicalProtocolOracleViewCosted, canonicalProtocolOracleViewBudget]
  nlinarith only [hc, hr]

end Zcash.Snark.ZeroKnowledge
