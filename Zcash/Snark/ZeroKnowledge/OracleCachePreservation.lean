import Zcash.Snark.ZeroKnowledge.OracleContinuationResources

/-!
# Persistence of oracle answers through real and simulated attempts

An existing answer cannot change during a cached execution or successful trace
programming. Explicit programming failure retains the entire prior cache.
These facts support retries that use one evolving oracle state.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common

/-- Every completed cached-tape execution preserves each previously stored oracle answer. -/
theorem cachedOracleRunTape_keeps {Query Reply Value : Type*} [DecidableEq Query]
    (budget : ℕ) (comp : OracleComp Query Reply Value) (cache : OracleCache Query Reply)
    (tape : Fin budget → Reply) (view : Value × OracleCache Query Reply)
    (hrun : cachedOracleRunTape budget comp cache tape = some view)
    (query : Query) (reply : Reply) (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup view.2 query = some reply := by
  induction budget generalizing comp cache view with
  | zero =>
    cases comp with
    | pure value => cases Option.some.inj hrun; exact hstored
    | query address next => simp [cachedOracleRunTape] at hrun
  | succ budget ih =>
    cases comp with
    | pure value => cases Option.some.inj hrun; exact hstored
    | query address next =>
      cases hlookup : oracleCacheLookup cache address with
      | some answer =>
        exact ih (next answer) cache (Fin.tail tape) view
          (by simpa only [cachedOracleRunTape, hlookup] using hrun) hstored
      | none =>
        have hne : address ≠ query := by
          intro heq
          subst address
          rw [hstored] at hlookup
          contradiction
        exact ih (next (tape 0)) ((address, tape 0) :: cache) (Fin.tail tape) view
          (by simpa only [cachedOracleRunTape, hlookup] using hrun)
          (by simpa only [oracleCacheLookup_cons_ne cache address query (tape 0) hne] using hstored)

/-- Every supported bounded lazy-oracle execution preserves every earlier answer. -/
theorem cachedOracleLaw_keeps {Query Reply Value : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) {comp : OracleComp Query Reply Value} {budget : ℕ}
    (hbudget : comp.QueryBound budget) (cache : OracleCache Query Reply)
    (view : Value × OracleCache Query Reply) (hview : view ∈ (cachedOracleLaw answerLaw comp cache).support)
    (query : Query) (reply : Reply) (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup view.2 query = some reply := by
  have hsome : some view ∈ ((independentTapeLaw answerLaw budget).map
      (cachedOracleRunTape budget comp cache)).support := by
    rw [cachedOracleRunTape_law answerLaw hbudget cache]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨view, hview, rfl⟩
  obtain ⟨tape, _, hrun⟩ := (PMF.mem_support_map_iff _ _ _).mp hsome
  exact cachedOracleRunTape_keeps budget comp cache tape view hrun query reply hstored

/-- Programming preserves old answers, including when failure returns the unchanged prior table. -/
theorem programOracleView_attemptCache_keeps {Query Reply Value : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (view : Value × List (Query × Reply))
    (query : Query) (reply : Reply) (hstored : oracleCacheLookup cache query = some reply) :
    oracleCacheLookup (oracleAttemptCache cache (programOracleView cache view)) query = some reply := by
  cases hprogram : programOracleTrace cache view.2 with
  | none =>
    simpa only [programOracleView, hprogram, Option.map_none, oracleAttemptCache, Option.getD_none] using hstored
  | some finalCache =>
    simpa only [programOracleView, hprogram, Option.map_some, oracleAttemptCache, Option.getD_some] using
      programOracleTrace_keeps view.2 cache finalCache hprogram query reply hstored

end Zcash.Snark.ZeroKnowledge
