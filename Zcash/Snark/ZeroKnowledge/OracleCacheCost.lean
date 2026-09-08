import Zcash.Snark.ZeroKnowledge.ByteEqualityCost
import Zcash.Snark.ZeroKnowledge.OracleProgramming

/-!
# Structural cost of the original byte-oracle cache lookup

The cache is the same finite list of materialized address/answer pairs. Each
visited entry costs its checked byte comparison, one cache case test, and one
branch; reaching the empty cache costs one case test. Stored answers are returned
as data. Comparison reads the query first, and the erasure theorem proves the
same first-match semantics as the original address-first equality predicate.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Costed lookup in the original finite byte-address cache. -/
def oracleCacheLookupCosted {Reply : Type} :
    OracleCache TranscriptHashAddress Reply → TranscriptHashAddress → Option Reply × ℕ
  | [], _ => (none, 1)
  | (address, answer) :: rest, query =>
    let comparison := transcriptAddressEqCosted query address
    if comparison.1 then (some answer, comparison.2 + 2)
    else
      let next := oracleCacheLookupCosted rest query
      (next.1, comparison.2 + next.2 + 2)

/-- Cost erasure preserves the first-match behavior of the existing oracle cache. -/
theorem oracleCacheLookupCosted_result {Reply : Type}
    (cache : OracleCache TranscriptHashAddress Reply) (query : TranscriptHashAddress) :
    (oracleCacheLookupCosted cache query).1 = oracleCacheLookup cache query := by
  induction cache with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨address, answer⟩
    by_cases heq : address = query
    · subst address
      simp [oracleCacheLookupCosted, transcriptAddressEqCosted_result,
        oracleCacheLookup_cons_same]
    · have hreverse : query ≠ address := Ne.symm heq
      simp [oracleCacheLookupCosted, transcriptAddressEqCosted_result, heq, hreverse,
        oracleCacheLookup_cons_ne, ih]

/-- Lookup cost grows with the cache length and the materialized query's byte length. -/
theorem oracleCacheLookupCosted_cost_le {Reply : Type}
    (cache : OracleCache TranscriptHashAddress Reply) (query : TranscriptHashAddress) :
    (oracleCacheLookupCosted cache query).2 ≤
      cache.length * (2 * (query.1.length + query.2.length) + 5) + 1 := by
  induction cache with
  | nil => simp [oracleCacheLookupCosted]
  | cons entry rest ih =>
    rcases entry with ⟨address, answer⟩
    have hc := transcriptAddressEqCosted_cost_le query address
    by_cases heq : (transcriptAddressEqCosted query address).1 = true
    · simp only [oracleCacheLookupCosted, if_pos heq, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [oracleCacheLookupCosted, if_neg heq, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end Zcash.Snark.ZeroKnowledge
