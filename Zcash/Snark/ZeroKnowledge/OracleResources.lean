import Zcash.Snark.ZeroKnowledge.OracleProgramming

/-!
# Finite oracle query and cache budgets

The tape budget bounds the recorded query count and the cache growth on every
execution. These are oracle-resource bounds; they do not assert a running-time
bound for an arbitrary supplied continuation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common

/-- The recorded independent-query trace uses at most its assigned number of reply slots. -/
theorem freshOracleRunTape_length_le {Query Reply Value : Type*}
    (budget : ℕ) (comp : OracleComp Query Reply Value) (tape : Fin budget → Reply)
    (view : Value × List (Query × Reply)) (hrun : freshOracleRunTape budget comp tape = some view) :
    view.2.length ≤ budget := by
  induction budget generalizing comp view with
  | zero =>
    cases comp with
    | pure value => cases Option.some.inj hrun; exact Nat.zero_le _
    | query query next => simp [freshOracleRunTape] at hrun
  | succ budget ih =>
    cases comp with
    | pure value => cases Option.some.inj hrun; exact Nat.zero_le _
    | query query next =>
      cases hrest : freshOracleRunTape budget (next (tape 0)) (Fin.tail tape) with
      | none => simp [freshOracleRunTape, hrest] at hrun
      | some rest =>
        have heq : (rest.1, (query, tape 0) :: rest.2) = view := by
          simpa only [freshOracleRunTape, hrest, Option.map_some, Option.some.injEq] using hrun
        subst view
        exact Nat.succ_le_succ (ih _ _ _ hrest)

/-- Successful programming stores exactly one new entry for every proposed query. -/
theorem programOracleTrace_length {Query Reply : Type*} [DecidableEq Query]
    (trace : List (Query × Reply)) (cache finalCache : OracleCache Query Reply)
    (hprogram : programOracleTrace cache trace = some finalCache) :
    finalCache.length = cache.length + trace.length := by
  induction trace generalizing cache with
  | nil =>
    cases Option.some.inj hprogram
    simp
  | cons entry trace ih =>
    rcases entry with ⟨query, reply⟩
    cases hlookup : oracleCacheLookup cache query with
    | some value => simp [programOracleTrace, hlookup] at hprogram
    | none =>
      have h := ih ((query, reply) :: cache) (by simpa only [programOracleTrace, hlookup] using hprogram)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 trace.length] using h

/-- Every cached execution adds at most its total query budget to the initial table. -/
theorem cachedOracleRunTape_cache_length_le {Query Reply Value : Type*} [DecidableEq Query]
    (budget : ℕ) (comp : OracleComp Query Reply Value) (cache : OracleCache Query Reply)
    (tape : Fin budget → Reply) (view : Value × OracleCache Query Reply)
    (hrun : cachedOracleRunTape budget comp cache tape = some view) :
    view.2.length ≤ cache.length + budget := by
  induction budget generalizing comp cache view with
  | zero =>
    cases comp with
    | pure value => cases Option.some.inj hrun; exact Nat.le_add_right _ _
    | query query next => simp [cachedOracleRunTape] at hrun
  | succ budget ih =>
    cases comp with
    | pure value => cases Option.some.inj hrun; exact Nat.le_add_right _ _
    | query query next =>
      cases hlookup : oracleCacheLookup cache query with
      | some reply =>
        have h := ih (next reply) cache (Fin.tail tape) view
          (by simpa only [cachedOracleRunTape, hlookup] using hrun)
        omega
      | none =>
        have h := ih (next (tape 0)) ((query, tape 0) :: cache) (Fin.tail tape) view
          (by simpa only [cachedOracleRunTape, hlookup] using hrun)
        simp only [List.length_cons] at h
        omega

end Zcash.Snark.ZeroKnowledge
