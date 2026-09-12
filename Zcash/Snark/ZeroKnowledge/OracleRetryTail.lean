import Zcash.Snark.ZeroKnowledge.OracleRetry

/-!
# Oracle programming preserves the stopping policy

The auxiliary caller can repeat only a successfully programmed ordinary attempt.
A programming conflict stops this composition. The released proof call has no
such caller policy.
-/

namespace Zcash.Snark.ZeroKnowledge

open scoped ENNReal

/-- Programming an observation cannot add an invocation that the auxiliary caller would reject. -/
theorem programOracleView_retry_imp {Query Reply : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (view : ProverAttemptResult × List (Query × Reply))
    (h : (programOracleView cache view).map Prod.fst ∈ oracleRetrySet) :
    callerRetryAfterFailure view.1.status = true := by
  unfold programOracleView at h
  cases hp : programOracleTrace cache view.2 with
  | none => simp [hp, oracleRetrySet, oracleRetryRequested] at h
  | some next =>
    simpa only [hp, Option.map_some, oracleRetrySet, Set.mem_setOf_eq,
      oracleRetryRequested_some] using h

/-- Refusing a programming conflict cannot increase the retry mass of any source law. -/
theorem programOracleView_retry_le {Seed Query Reply : Type*} [DecidableEq Query]
    (law : PMF Seed) (cache : OracleCache Query Reply)
    (view : Seed → ProverAttemptResult × List (Query × Reply)) :
    (law.map (fun seed => oracleAttemptState cache (programOracleView cache (view seed)))).toOuterMeasure
        {observation | observation.1 ∈ oracleRetrySet} ≤
      (law.map (fun seed => (view seed).1)).toOuterMeasure
        {attempt | callerRetryAfterFailure attempt.status = true} := by
  simp only [PMF.toOuterMeasure_map_apply]
  apply law.toOuterMeasure.mono
  intro seed hseed
  exact programOracleView_retry_imp cache (view seed) hseed

end Zcash.Snark.ZeroKnowledge
