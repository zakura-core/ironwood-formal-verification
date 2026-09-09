import Zcash.Snark.ZeroKnowledge.CachedPrefixCost

namespace Zcash.Snark.ZeroKnowledge

/-- Fixed envelope for the complete bounded cache run, including every history traversal and byte comparison. -/
def cachedPrefixRunCostBudget
    (budget historyBound cacheBound addressWidth reportPrice checkPrice queryPrice replyPrice : ℕ) : ℕ :=
  (budget + 1) * (2 * historyBound + reportPrice + checkPrice + queryPrice + replyPrice +
    cacheBound * (2 * addressWidth + 5) + 25) + 1

set_option maxHeartbeats 600000 in
/-- The full online run obeys one polynomial bound on all hit, miss, and stopping branches. -/
theorem cachedPrefixRunCosted_cost_le {Reply Value : Type}
    (report : List Reply → ℕ → Value × ℕ) (continues : Value → Bool × ℕ)
    (query : List Reply → ℕ → TranscriptHashAddress × ℕ) (reply : ℕ → Reply × ℕ)
    (historyBound cacheBound addressWidth reportPrice checkPrice queryPrice replyPrice : ℕ)
    (hreport : ∀ history, history.length ≤ historyBound → (report history history.length).2 ≤ reportPrice)
    (hcheck : ∀ value, (continues value).2 ≤ checkPrice)
    (hquery : ∀ history, history.length ≤ historyBound → (query history history.length).2 ≤ queryPrice)
    (hwidth : ∀ history, history.length ≤ historyBound →
      (query history history.length).1.1.length + (query history history.length).1.2.length ≤ addressWidth)
    (hreply : ∀ cursor, (reply cursor).2 ≤ replyPrice)
    (budget : ℕ) (history : List Reply) (cache : OracleCache TranscriptHashAddress Reply) (cursor : ℕ)
    (hhistory : history.length + budget ≤ historyBound) (hcache : cache.length + budget ≤ cacheBound) :
    (cachedPrefixRunCosted report continues query reply budget history cache cursor).2 ≤
      cachedPrefixRunCostBudget budget historyBound cacheBound addressWidth reportPrice checkPrice queryPrice replyPrice := by
  let step := 2 * historyBound + reportPrice + checkPrice + queryPrice + replyPrice +
    cacheBound * (2 * addressWidth + 5) + 25
  induction budget generalizing history cache cursor with
  | zero =>
    have hr := hreport history (by omega)
    simp only [cachedPrefixRunCosted, lengthListCosted_result, lengthListCosted_cost,
      cachedPrefixRunCostBudget, Nat.zero_add, Nat.one_mul]
    omega
  | succ budget ih =>
    have hr := hreport history (by omega)
    have hc := hcheck (report history history.length).1
    have hq := hquery history (by omega)
    have hw := hwidth history (by omega)
    have hp := hreply cursor
    have hl := oracleCacheLookupCosted_cost_le cache (query history history.length).1
    have hlookup : (oracleCacheLookupCosted cache (query history history.length).1).2 ≤
        cacheBound * (2 * addressWidth + 5) + 1 := hl.trans (by
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul (by omega) (by omega))
    have hstep : 2 * history.length + (report history history.length).2 +
        (continues (report history history.length).1).2 + (query history history.length).2 +
        (oracleCacheLookupCosted cache (query history history.length).1).2 + (reply cursor).2 + 17 ≤ step := by
      dsimp only [step]
      omega
    change (cachedPrefixRunCosted report continues query reply (budget + 1) history cache cursor).2 ≤
      (budget + 1 + 1) * step + 1
    rewrite [Nat.add_mul, Nat.one_mul]
    simp only [cachedPrefixRunCosted, lengthListCosted_result, lengthListCosted_cost,
      appendListCosted_result, appendListCosted_cost]
    split
    · split
      · rename_i answer _
        have hn := ih (history ++ [answer]) cache (cursor + 1)
          (by simp only [List.length_append, List.length_singleton]; omega) (by omega)
        change (cachedPrefixRunCosted report continues query reply budget (history ++ [answer]) cache (cursor + 1)).2 ≤
          (budget + 1) * step + 1 at hn
        omega
      · have hn := ih (history ++ [(reply cursor).1]) (( (query history history.length).1, (reply cursor).1) :: cache)
          (cursor + 1) (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_cons]; omega)
        change (cachedPrefixRunCosted report continues query reply budget (history ++ [(reply cursor).1])
          (((query history history.length).1, (reply cursor).1) :: cache) (cursor + 1)).2 ≤
          (budget + 1) * step + 1 at hn
        omega
    · omega

end Zcash.Snark.ZeroKnowledge
