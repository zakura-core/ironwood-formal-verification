import Zcash.Snark.ZeroKnowledge.CachedPrefixCost

namespace Zcash.Snark.ZeroKnowledge

/-- Source erasure needs producer agreement only at histories reachable within the supplied finite capacity. -/
theorem cachedPrefixRunCosted_result_of_history_bound {Reply Value : Type}
    (fallback : Reply) (sourceReport : (ℕ → Reply) → ℕ → Value) (sourceContinues : Value → Bool)
    (sourceQuery : (ℕ → Reply) → ℕ → TranscriptHashAddress)
    (report : List Reply → ℕ → Value × ℕ) (continues : Value → Bool × ℕ)
    (query : List Reply → ℕ → TranscriptHashAddress × ℕ) (reply : ℕ → Reply × ℕ)
    (historyBound : ℕ)
    (hreport : ∀ history, history.length ≤ historyBound → ∀ index, (report history index).1 = sourceReport (oracleHistoryTape fallback history) index)
    (hcheck : ∀ value, (continues value).1 = sourceContinues value)
    (hquery : ∀ history, history.length ≤ historyBound → ∀ index, (query history index).1 = sourceQuery (oracleHistoryTape fallback history) index)
    (budget : ℕ) (history : List Reply) (cache : OracleCache TranscriptHashAddress Reply) (cursor : ℕ)
    (hhistory : history.length + budget ≤ historyBound) :
    some (cachedPrefixRunCosted report continues query reply budget history cache cursor).1 =
      cachedOracleRunTape budget (prefixOracleComp fallback sourceReport sourceContinues sourceQuery budget history)
        cache (fun index => (reply (cursor + index.val)).1) := by
  induction budget generalizing history cache cursor with
  | zero =>
    have hh : history.length ≤ historyBound := by omega
    simp only [cachedPrefixRunCosted, prefixOracleComp, cachedOracleRunTape,
      lengthListCosted_result, hreport history hh]
  | succ budget ih =>
    have hh : history.length ≤ historyBound := by omega
    have htail : Fin.tail (fun index : Fin (budget + 1) => (reply (cursor + index.val)).1) =
        (fun index : Fin budget => (reply (cursor + 1 + index.val)).1) := by
      funext index
      simp only [Fin.tail, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
    simp only [cachedPrefixRunCosted, prefixOracleComp, lengthListCosted_result, hreport history hh, hcheck, hquery history hh]
    cases hcontinue : sourceContinues (sourceReport (oracleHistoryTape fallback history) history.length) with
    | false => simp only [Bool.false_eq_true, if_false, cachedOracleRunTape]
    | true =>
      simp only [if_true, cachedOracleRunTape, oracleCacheLookupCosted_result, htail,
        Fin.val_zero, Nat.add_zero, appendListCosted_result]
      cases hlookup : oracleCacheLookup cache (sourceQuery (oracleHistoryTape fallback history) history.length) with
      | none => exact ih _ _ _ (by simp only [List.length_append, List.length_singleton]; omega)
      | some answer => exact ih _ _ _ (by simp only [List.length_append, List.length_singleton]; omega)

end Zcash.Snark.ZeroKnowledge
