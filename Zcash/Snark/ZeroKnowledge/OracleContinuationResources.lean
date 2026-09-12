import Zcash.Snark.ZeroKnowledge.OracleContinuation
import Zcash.Snark.ZeroKnowledge.OracleTableResources

/-!
# Cache budgets through a proof observation

An explicit simulator failure keeps the old table. Otherwise postprocessing
uses the table returned with the attempt. Query bounds then control every
supported final cache, including after an incomplete attempt.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common

/-- The cache exposed to a subsequent oracle computation, retaining the prior table on programming failure. -/
def oracleAttemptCache {Query Reply Attempt : Type*} (priorCache : OracleCache Query Reply)
    (observation : Option (Attempt × OracleCache Query Reply)) : OracleCache Query Reply :=
  (observation.map Prod.snd).getD priorCache

/-- Programming an attempt adds at most its proposed query count, even when it fails. -/
theorem programOracleView_cache_length_le {Query Reply Value : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (view : Value × List (Query × Reply)) :
    (oracleAttemptCache cache (programOracleView cache view)).length ≤ cache.length + view.2.length := by
  cases hprogram : programOracleView cache view with
  | none => simp only [oracleAttemptCache, Option.map_none, Option.getD_none]; omega
  | some output =>
    simp only [oracleAttemptCache, Option.map_some, Option.getD_some]
    exact (programOracleView_cache_length cache view output hprogram).le

/-- A bounded adaptive continuation adds at most its query budget to the retained attempt cache. -/
theorem oracleAttemptContinue_cache_length_le {Query Reply Attempt Output : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) (priorCache : OracleCache Query Reply)
    (after : Option Attempt → OracleComp Query Reply Output) {budget : ℕ}
    (hbudget : ∀ result, (after result).QueryBound budget)
    (observation : Option (Attempt × OracleCache Query Reply))
    (output : Output × OracleCache Query Reply)
    (houtput : output ∈ (oracleAttemptContinue answerLaw priorCache after observation).support) :
    output.2.length ≤ (oracleAttemptCache priorCache observation).length + budget := by
  cases observation with
  | none => exact cachedOracleLaw_cache_length_le answerLaw (hbudget none) priorCache output houtput
  | some observed =>
    exact cachedOracleLaw_cache_length_le answerLaw (hbudget (some observed.1)) observed.2 output houtput

end Zcash.Snark.ZeroKnowledge
