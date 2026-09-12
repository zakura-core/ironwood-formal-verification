import Zcash.Snark.ZeroKnowledge.ProtocolOracle
import Zcash.Snark.ZeroKnowledge.OracleResources

/-!
# Query and table sizes for a programmed protocol attempt

An observed prefix never programs more addresses than the complete receive
schedule. Successful programming adds exactly that many new entries and keeps
the previous table intact.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The retained oracle log cannot exceed the original protocol's number of receives. -/
theorem protocolOracleView_queries_length_le (pointCodec : VestaG → Option (List UInt8))
    (initial trace : List (TranscriptElt Fp VestaG)) (digests : ℕ → Fin challengeDigestCard)
    (check : ℕ → Option ProverAttemptFailure) :
    (protocolOracleView pointCodec initial digests check trace).2.length ≤ protocolChallengeCount trace := by
  have h := (replayOracleSchedule_queries_prefix
    (protocolOracleReport pointCodec digests check trace) protocolAttemptContinues
    (protocolQueryAddress initial trace) digests (protocolChallengeCount trace) 0).length_le
  simpa only [List.length_map, List.length_range'] using h

/-- A programmed view stores exactly the number of addresses in its proposed query log. -/
theorem programOracleView_cache_length {Query Reply Value : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (view : Value × List (Query × Reply))
    (output : Value × OracleCache Query Reply) (hprogram : programOracleView cache view = some output) :
    output.2.length = cache.length + view.2.length := by
  cases hcache : programOracleTrace cache view.2 with
  | none => simp only [programOracleView, hcache, Option.map_none, reduceCtorEq] at hprogram
  | some finalCache =>
    have heq : (view.1, finalCache) = output := by
      simpa only [programOracleView, hcache, Option.map_some, Option.some.injEq] using hprogram
    rw [← heq]
    exact programOracleTrace_length _ _ _ hcache

end Zcash.Snark.ZeroKnowledge
