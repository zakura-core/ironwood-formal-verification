import Zcash.Snark.ZeroKnowledge.OracleSchedule
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

/-! # Complete structural cost of the original stopping oracle replay -/

namespace Zcash.Snark.ZeroKnowledge

/-- Replay the original policy while retaining every report, query, and reply producer. -/
def replayOracleScheduleCosted {Query Reply Value : Type*}
    (report : ℕ → Value × ℕ) (continues : Value → Bool × ℕ)
    (query : ℕ → Query × ℕ) (reply : ℕ → Reply × ℕ) :
    ℕ → ℕ → (Value × List (Query × Reply)) × ℕ
  | 0, index =>
    let current := report index
    ((current.1, []), current.2 + 2)
  | budget + 1, index =>
    let current := report index
    let check := continues current.1
    if check.1 then
      let address := query index
      let response := reply index
      let rest := replayOracleScheduleCosted report continues query reply budget (index + 1)
      ((rest.1.1, (address.1, response.1) :: rest.1.2),
        current.2 + check.2 + address.2 + response.2 + rest.2 + 8)
    else ((current.1, []), current.2 + check.2 + 5)

/-- The counted replay has exactly the original result and retained query/response prefix. -/
theorem replayOracleScheduleCosted_result {Query Reply Value : Type*}
    (report : ℕ → Value × ℕ) (continues : Value → Bool × ℕ)
    (query : ℕ → Query × ℕ) (reply : ℕ → Reply × ℕ) (budget index : ℕ) :
    (replayOracleScheduleCosted report continues query reply budget index).1 =
      replayOracleSchedule (fun index => (report index).1) (fun value => (continues value).1)
        (fun index => (query index).1) (fun index => (reply index).1) budget index := by
  induction budget generalizing index with
  | zero => rfl
  | succ budget ih =>
    cases h : (continues (report index).1).1 <;>
      simp only [replayOracleScheduleCosted, replayOracleSchedule, h, Bool.false_eq_true,
        if_false, if_true, ih]

/-- The full finite replay is bounded independently of every stopping decision. -/
theorem replayOracleScheduleCosted_cost_le {Query Reply Value : Type*}
    (report : ℕ → Value × ℕ) (continues : Value → Bool × ℕ)
    (query : ℕ → Query × ℕ) (reply : ℕ → Reply × ℕ)
    (reportPrice checkPrice queryPrice replyPrice : ℕ)
    (hreport : ∀ index, (report index).2 ≤ reportPrice)
    (hcheck : ∀ value, (continues value).2 ≤ checkPrice)
    (hquery : ∀ index, (query index).2 ≤ queryPrice)
    (hreply : ∀ index, (reply index).2 ≤ replyPrice)
    (budget index : ℕ) :
    (replayOracleScheduleCosted report continues query reply budget index).2 ≤
      (budget + 1) * (reportPrice + checkPrice + queryPrice + replyPrice + 10) + 1 := by
  induction budget generalizing index with
  | zero =>
    have h := hreport index
    simp only [replayOracleScheduleCosted, Nat.zero_add, Nat.one_mul]
    omega
  | succ budget ih =>
    have hr := hreport index
    have hc := hcheck (report index).1
    have hq := hquery index
    have hp := hreply index
    have hn := ih (index + 1)
    cases h : (continues (report index).1).1 <;>
      simp only [replayOracleScheduleCosted, h, Bool.false_eq_true, if_false, if_true]
    · nlinarith only [hr, hc]
    · nlinarith only [hr, hc, hq, hp, hn]

end Zcash.Snark.ZeroKnowledge
