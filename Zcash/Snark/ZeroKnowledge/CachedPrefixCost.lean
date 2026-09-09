import Zcash.Snark.ZeroKnowledge.OracleCacheCost
import Zcash.Snark.ZeroKnowledge.OracleSchedule
import Zcash.Snark.ZeroKnowledge.ListTraversalCost

/-!
# Counted execution of the original cached prefix oracle

Reports and addresses are recomputed from the received history at each step.
Every cache hit retains the original answer and still advances the independent
reply-tape cursor. Misses insert the new pair before continuing. The complete
history traversal, append, byte-cache lookup, and producer costs are retained.
The source and bound theorems expose the producer obligations; concrete Action
composition discharges them with the complete counted real prover.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Run the bounded online prefix policy against the actual first-match byte cache. -/
def cachedPrefixRunCosted {Reply Value : Type}
    (report : List Reply → ℕ → Value × ℕ) (continues : Value → Bool × ℕ)
    (query : List Reply → ℕ → TranscriptHashAddress × ℕ) (reply : ℕ → Reply × ℕ) :
    ℕ → List Reply → OracleCache TranscriptHashAddress Reply → ℕ →
      (Value × OracleCache TranscriptHashAddress Reply) × ℕ
  | 0, history, cache, _ =>
    let index := lengthListCosted history
    let current := report history index.1
    ((current.1, cache), index.2 + current.2 + 3)
  | budget + 1, history, cache, cursor =>
    let index := lengthListCosted history
    let current := report history index.1
    let check := continues current.1
    if check.1 then
      let address := query history index.1
      let found := oracleCacheLookupCosted cache address.1
      match found.1 with
      | some answer =>
        let extended := appendListCosted history [answer]
        let rest := cachedPrefixRunCosted report continues query reply budget extended.1 cache (cursor + 1)
        (rest.1, index.2 + current.2 + check.2 + address.2 + found.2 + extended.2 + rest.2 + 12)
      | none =>
        let answer := reply cursor
        let extended := appendListCosted history [answer.1]
        let rest := cachedPrefixRunCosted report continues query reply budget extended.1
          ((address.1, answer.1) :: cache) (cursor + 1)
        (rest.1, index.2 + current.2 + check.2 + address.2 + found.2 + answer.2 + extended.2 + rest.2 + 15)
    else ((current.1, cache), index.2 + current.2 + check.2 + 5)

/-- Erasure gives the literal cached prefix computation, including reused answers and consumed hit slots. -/
theorem cachedPrefixRunCosted_result {Reply Value : Type}
    (fallback : Reply) (sourceReport : (ℕ → Reply) → ℕ → Value) (sourceContinues : Value → Bool)
    (sourceQuery : (ℕ → Reply) → ℕ → TranscriptHashAddress)
    (report : List Reply → ℕ → Value × ℕ) (continues : Value → Bool × ℕ)
    (query : List Reply → ℕ → TranscriptHashAddress × ℕ) (reply : ℕ → Reply × ℕ)
    (hreport : ∀ history index, (report history index).1 = sourceReport (oracleHistoryTape fallback history) index)
    (hcheck : ∀ value, (continues value).1 = sourceContinues value)
    (hquery : ∀ history index, (query history index).1 = sourceQuery (oracleHistoryTape fallback history) index)
    (budget : ℕ) (history : List Reply) (cache : OracleCache TranscriptHashAddress Reply) (cursor : ℕ) :
    some (cachedPrefixRunCosted report continues query reply budget history cache cursor).1 =
      cachedOracleRunTape budget (prefixOracleComp fallback sourceReport sourceContinues sourceQuery budget history)
        cache (fun index => (reply (cursor + index.val)).1) := by
  induction budget generalizing history cache cursor with
  | zero => simp only [cachedPrefixRunCosted, prefixOracleComp, cachedOracleRunTape,
      lengthListCosted_result, hreport]
  | succ budget ih =>
    have htail : Fin.tail (fun index : Fin (budget + 1) => (reply (cursor + index.val)).1) =
        (fun index : Fin budget => (reply (cursor + 1 + index.val)).1) := by
      funext index
      simp only [Fin.tail, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
    simp only [cachedPrefixRunCosted, prefixOracleComp, lengthListCosted_result, hreport, hcheck, hquery]
    cases hcontinue : sourceContinues (sourceReport (oracleHistoryTape fallback history) history.length) with
    | false => simp only [Bool.false_eq_true, if_false, cachedOracleRunTape]
    | true =>
      simp only [if_true, cachedOracleRunTape, oracleCacheLookupCosted_result, htail,
        Fin.val_zero, Nat.add_zero, appendListCosted_result]
      cases hlookup : oracleCacheLookup cache (sourceQuery (oracleHistoryTape fallback history) history.length) with
      | none => exact ih _ _ _
      | some answer => exact ih _ _ _

/-- At most one cache entry is inserted per remaining query, regardless of report outcomes. -/
theorem cachedPrefixRunCosted_cache_length_le {Reply Value : Type}
    (report : List Reply → ℕ → Value × ℕ) (continues : Value → Bool × ℕ)
    (query : List Reply → ℕ → TranscriptHashAddress × ℕ) (reply : ℕ → Reply × ℕ)
    (budget : ℕ) (history : List Reply) (cache : OracleCache TranscriptHashAddress Reply) (cursor : ℕ) :
    (cachedPrefixRunCosted report continues query reply budget history cache cursor).1.2.length ≤ cache.length + budget := by
  induction budget generalizing history cache cursor with
  | zero => simp only [cachedPrefixRunCosted, Nat.add_zero, le_refl]
  | succ budget ih =>
    simp only [cachedPrefixRunCosted]
    split
    · split
      · exact (ih _ _ _).trans (by omega)
      · exact (ih _ _ _).trans (by simp only [List.length_cons]; omega)
    · change cache.length ≤ cache.length + (budget + 1)
      omega

end Zcash.Snark.ZeroKnowledge
