import Zcash.Snark.ZeroKnowledge.OracleCacheCost

/-!
# Structural costs of conflict-checked oracle programming

This is the cache phase on an already materialized chronological query log.
In addition to the byte-comparison and lookup counters, each trace case and
lookup-result branch costs one unit; a new cache cell costs one unit. Mapping
the final option costs one unit. The counter remains outside the failure option,
so a conflict never discards the work already performed. Constructing the input
view, including its proof and address bytes, is a separate runtime obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Execute original conflict-checked programming while retaining the cost of failed prefixes. -/
def programOracleTraceCosted {Reply : Type} (cache : OracleCache TranscriptHashAddress Reply) :
    List (TranscriptHashAddress × Reply) → Option (OracleCache TranscriptHashAddress Reply) × ℕ
  | [] => (some cache, 1)
  | (query, reply) :: rest =>
    let lookup := oracleCacheLookupCosted cache query
    match lookup.1 with
    | some _ => (none, lookup.2 + 2)
    | none =>
      let next := programOracleTraceCosted ((query, reply) :: cache) rest
      (next.1, lookup.2 + next.2 + 3)

/-- Erasure gives the original programming result, including every collision failure. -/
theorem programOracleTraceCosted_result {Reply : Type}
    (trace : List (TranscriptHashAddress × Reply)) (cache : OracleCache TranscriptHashAddress Reply) :
    (programOracleTraceCosted cache trace).1 = programOracleTrace cache trace := by
  induction trace generalizing cache with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨query, reply⟩
    simp only [programOracleTraceCosted, oracleCacheLookupCosted_result, programOracleTrace]
    cases hlookup : oracleCacheLookup cache query with
    | none => exact ih ((query, reply) :: cache)
    | some answer => rfl

/-- A fixed upper bound for the cache plus remaining trace bounds every lookup along the run. -/
theorem programOracleTraceCosted_cost_le_capacity {Reply : Type}
    (trace : List (TranscriptHashAddress × Reply)) (cache : OracleCache TranscriptHashAddress Reply)
    (capacity queryBytes : ℕ) (hcapacity : cache.length + trace.length ≤ capacity)
    (hbytes : ∀ entry ∈ trace, entry.1.1.length + entry.1.2.length ≤ queryBytes) :
    (programOracleTraceCosted cache trace).2 ≤
      trace.length * (capacity * (2 * queryBytes + 5) + 4) + 1 := by
  induction trace generalizing cache with
  | nil => simp [programOracleTraceCosted]
  | cons entry rest ih =>
    rcases entry with ⟨query, reply⟩
    have hquery : query.1.length + query.2.length ≤ queryBytes :=
      hbytes (query, reply) List.mem_cons_self
    have hcache : cache.length ≤ capacity := by
      simp only [List.length_cons] at hcapacity
      omega
    have hlookup : (oracleCacheLookupCosted cache query).2 ≤ capacity * (2 * queryBytes + 5) + 1 :=
      (oracleCacheLookupCosted_cost_le cache query).trans
        (Nat.add_le_add_right (Nat.mul_le_mul hcache (by omega)) 1)
    have hrestCapacity : (((query, reply) :: cache).length + rest.length) ≤ capacity := by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcapacity
    have hrestBytes : ∀ entry ∈ rest, entry.1.1.length + entry.1.2.length ≤ queryBytes := by
      intro entry hentry
      exact hbytes entry (List.mem_cons_of_mem _ hentry)
    have hrest := ih ((query, reply) :: cache) hrestCapacity hrestBytes
    cases hfound : (oracleCacheLookupCosted cache query).1 with
    | none =>
      simp only [programOracleTraceCosted, hfound, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    | some answer =>
      simp only [programOracleTraceCosted, hfound, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The input trace length supplies a concrete cache-capacity envelope. -/
theorem programOracleTraceCosted_cost_le {Reply : Type}
    (trace : List (TranscriptHashAddress × Reply)) (cache : OracleCache TranscriptHashAddress Reply)
    (queryBytes : ℕ)
    (hbytes : ∀ entry ∈ trace, entry.1.1.length + entry.1.2.length ≤ queryBytes) :
    (programOracleTraceCosted cache trace).2 ≤
      trace.length * ((cache.length + trace.length) * (2 * queryBytes + 5) + 4) + 1 :=
  programOracleTraceCosted_cost_le_capacity trace cache _ queryBytes le_rfl hbytes

/-- A public upper bound on query count also bounds every stopped programming run. -/
theorem programOracleTraceCosted_cost_le_budget {Reply : Type}
    (trace : List (TranscriptHashAddress × Reply)) (cache : OracleCache TranscriptHashAddress Reply)
    (budget queryBytes : ℕ) (hbudget : trace.length ≤ budget)
    (hbytes : ∀ entry ∈ trace, entry.1.1.length + entry.1.2.length ≤ queryBytes) :
    (programOracleTraceCosted cache trace).2 ≤
      budget * ((cache.length + budget) * (2 * queryBytes + 5) + 4) + 1 := by
  exact (programOracleTraceCosted_cost_le_capacity trace cache _ queryBytes
    (Nat.add_le_add_left hbudget _) hbytes).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hbudget) 1)

/-- Program an already computed view and retain its work counter on failure. -/
def programOracleViewCosted {Reply Value : Type} (cache : OracleCache TranscriptHashAddress Reply)
    (view : Value × List (TranscriptHashAddress × Reply)) :
    Option (Value × OracleCache TranscriptHashAddress Reply) × ℕ :=
  let run := programOracleTraceCosted cache view.2
  (run.1.map (Prod.mk view.1), run.2 + 1)

/-- Erasure gives the existing view programmer, preserving its full success or failure result. -/
theorem programOracleViewCosted_result {Reply Value : Type}
    (cache : OracleCache TranscriptHashAddress Reply)
    (view : Value × List (TranscriptHashAddress × Reply)) :
    (programOracleViewCosted cache view).1 = programOracleView cache view := by
  simp only [programOracleViewCosted, programOracleTraceCosted_result, programOracleView]

/-- A byte-size and query-count envelope bounds the cache phase of the complete view. -/
theorem programOracleViewCosted_cost_le {Reply Value : Type}
    (cache : OracleCache TranscriptHashAddress Reply)
    (view : Value × List (TranscriptHashAddress × Reply)) (budget queryBytes : ℕ)
    (hbudget : view.2.length ≤ budget)
    (hbytes : ∀ entry ∈ view.2, entry.1.1.length + entry.1.2.length ≤ queryBytes) :
    (programOracleViewCosted cache view).2 ≤
      budget * ((cache.length + budget) * (2 * queryBytes + 5) + 4) + 2 := by
  have h := programOracleTraceCosted_cost_le_budget view.2 cache budget queryBytes hbudget hbytes
  change (programOracleTraceCosted cache view.2).2 + 1 ≤ _
  omega

end Zcash.Snark.ZeroKnowledge
