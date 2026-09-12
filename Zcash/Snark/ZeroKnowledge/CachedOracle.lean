import Zcash.Snark.ZeroKnowledge.RandomTapeSource

/-!
# A lazy random oracle with a retained finite cache

Every fresh address receives one independent answer. Repeated queries return the
cached answer without drawing another one. The cache is also retained as output,
so arbitrary later oracle computations can continue from precisely the same state.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common

/-- A finite address/answer table, with the newest entry first. -/
abbrev OracleCache (Query Reply : Type*) := List (Query × Reply)

/-- Read the first stored answer to an address. -/
def oracleCacheLookup {Query Reply : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (query : Query) : Option Reply :=
  (cache.find? (fun entry => entry.1 = query)).map Prod.snd

/-- An empty oracle cache has no answers. -/
theorem oracleCacheLookup_nil {Query Reply : Type*} [DecidableEq Query] (query : Query) :
    oracleCacheLookup ([] : OracleCache Query Reply) query = none := rfl

/-- The most recently stored answer is read at its address. -/
theorem oracleCacheLookup_cons_same {Query Reply : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (query : Query) (reply : Reply) :
    oracleCacheLookup ((query, reply) :: cache) query = some reply := by
  simp [oracleCacheLookup]

/-- A new entry does not change answers at other addresses. -/
theorem oracleCacheLookup_cons_ne {Query Reply : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (query other : Query) (reply : Reply) (h : query ≠ other) :
    oracleCacheLookup ((query, reply) :: cache) other = oracleCacheLookup cache other := by
  simp [oracleCacheLookup, h]

/-- Cache membership is exactly whether the lookup returns an answer. -/
theorem oracleCacheLookup_eq_none {Query Reply : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) (query : Query) :
    oracleCacheLookup cache query = none ↔ query ∉ cache.map Prod.fst := by
  simp [oracleCacheLookup, List.find?_eq_none]
  constructor
  · intro h reply hmem
    exact h query reply hmem rfl
  · intro h other reply hmem heq
    subst other
    exact h reply hmem

/-- Answer repeated queries locally and return the resulting cache with the output. -/
def cacheOracleComp {Query Reply Value : Type*} [DecidableEq Query]
    (cache : OracleCache Query Reply) : OracleComp Query Reply Value →
      OracleComp Query Reply (Value × OracleCache Query Reply)
  | .pure value => .pure (value, cache)
  | .query query next =>
    match oracleCacheLookup cache query with
    | some reply => cacheOracleComp cache (next reply)
    | none => .query query (fun reply => cacheOracleComp ((query, reply) :: cache) (next reply))

/-- Caching cannot increase the number of oracle queries. -/
theorem cacheOracleComp_queryBound {Query Reply Value : Type*} [DecidableEq Query]
    {comp : OracleComp Query Reply Value} {budget : ℕ} (h : comp.QueryBound budget)
    (cache : OracleCache Query Reply) : (cacheOracleComp cache comp).QueryBound budget := by
  induction h generalizing cache with
  | pure value budget => exact .pure _ _
  | @query query next budget h ih =>
    simp only [cacheOracleComp]
    cases oracleCacheLookup cache query with
    | some reply => exact (ih reply cache).mono (Nat.le_succ _)
    | none => exact .query fun reply => ih reply ((query, reply) :: cache)

/-- The same lookup semantics as the original oracle tree on every consistent table. -/
theorem cacheOracleComp_run {Query Reply Value : Type*} [DecidableEq Query]
    (comp : OracleComp Query Reply Value) (table : Query → Reply)
    (cache : OracleCache Query Reply) (hcache : ∀ entry ∈ cache, table entry.1 = entry.2) :
    ((cacheOracleComp cache comp).run table).1 = comp.run table := by
  induction comp generalizing cache with
  | pure value => rfl
  | query query next ih =>
    simp only [cacheOracleComp]
    cases hlookup : oracleCacheLookup cache query with
    | some reply =>
      have hfind : ∃ entry, cache.find? (fun entry => entry.1 = query) = some entry ∧ entry.2 = reply := by
        simpa only [oracleCacheLookup, Option.map_eq_some_iff] using hlookup
      obtain ⟨entry, hfind, hreply⟩ := hfind
      have hquery : entry.1 = query := by simpa using List.find?_some hfind
      have ht : table query = reply := hquery ▸ (hcache entry (List.mem_of_find?_eq_some hfind)).trans hreply
      rw [ih reply cache hcache, OracleComp.run_query, ht]
    | none =>
      simp only [OracleComp.run_query]
      apply ih (table query) ((query, table query) :: cache)
      intro entry hentry
      rcases List.mem_cons.mp hentry with rfl | hentry
      · rfl
      · exact hcache entry hentry

/-- Lazy sampling at fresh addresses, retaining the oracle state for future queries. -/
noncomputable def cachedOracleLaw {Query Reply Value : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) (comp : OracleComp Query Reply Value) (cache : OracleCache Query Reply) :
    PMF (Value × OracleCache Query Reply) :=
  (cacheOracleComp cache comp).runFreshPMF answerLaw

/-- A fixed answer tape runs the cached oracle, consuming one slot per original query.

A cached query ignores its slot. This convention couples cached and independent
execution using equal-length tapes, without changing the lazy sampling law. -/
def cachedOracleRunTape {Query Reply Value : Type*} [DecidableEq Query] :
    (budget : ℕ) → OracleComp Query Reply Value → OracleCache Query Reply →
      (Fin budget → Reply) → Option (Value × OracleCache Query Reply)
  | _, .pure value, cache, _ => some (value, cache)
  | 0, .query _ _, _, _ => none
  | budget + 1, .query query next, cache, tape =>
    match oracleCacheLookup cache query with
    | some reply => cachedOracleRunTape budget (next reply) cache (Fin.tail tape)
    | none => cachedOracleRunTape budget (next (tape 0)) ((query, tape 0) :: cache) (Fin.tail tape)

/-- A structural query bound prevents tape exhaustion on every choice of answers. -/
theorem cachedOracleRunTape_ne_none {Query Reply Value : Type*} [DecidableEq Query]
    {comp : OracleComp Query Reply Value} {budget : ℕ} (h : comp.QueryBound budget)
    (cache : OracleCache Query Reply) (tape : Fin budget → Reply) :
    cachedOracleRunTape budget comp cache tape ≠ none := by
  induction h generalizing cache with
  | pure value budget => simp [cachedOracleRunTape]
  | @query query next budget h ih =>
    simp only [cachedOracleRunTape]
    cases oracleCacheLookup cache query with
    | some reply => exact ih reply cache (Fin.tail tape)
    | none => exact ih (tape 0) ((query, tape 0) :: cache) (Fin.tail tape)

/-- Independent tape slots implement precisely the lazy cached oracle distribution. -/
theorem cachedOracleRunTape_law {Query Reply Value : Type*} [DecidableEq Query]
    (answerLaw : PMF Reply) {comp : OracleComp Query Reply Value} {budget : ℕ}
    (h : comp.QueryBound budget) (cache : OracleCache Query Reply) :
    (independentTapeLaw answerLaw budget).map (cachedOracleRunTape budget comp cache) =
      (cachedOracleLaw answerLaw comp cache).map some := by
  induction h generalizing cache with
  | pure value budget =>
    have hconstant : cachedOracleRunTape budget (OracleComp.pure value) cache =
        fun _ => some (value, cache) := by
      funext tape
      cases budget <;> rfl
    rw [hconstant]
    simp only [cachedOracleLaw, cacheOracleComp, OracleComp.runFreshPMF, PMF.pure_map]
    exact PMF.map_const _ _
  | @query query next budget h ih =>
    simp only [independentTapeLaw, PMF.map_bind, PMF.map_comp, Function.comp_def,
      cachedOracleRunTape, Fin.cons_zero, Fin.tail_cons]
    cases hlookup : oracleCacheLookup cache query with
    | some reply =>
      simp only [PMF.bind_const]
      exact (ih reply cache).trans (by
        simp only [cachedOracleLaw, cacheOracleComp, hlookup])
    | none =>
      simp only [cachedOracleLaw, cacheOracleComp, hlookup, OracleComp.runFreshPMF, PMF.map_bind]
      congr 1
      funext reply
      exact ih reply ((query, reply) :: cache)

end Zcash.Snark.ZeroKnowledge
