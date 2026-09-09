import Zcash.Snark.ZeroKnowledge.OracleRetry

namespace Zcash.Snark.ZeroKnowledge

/-- Count the actual public observation/state adapter, keeping the old cache on absence. -/
def oracleAttemptStateCosted {Query Reply Attempt : Type*} (cache : OracleCache Query Reply) :
    Option (Attempt × OracleCache Query Reply) → (Option Attempt × OracleCache Query Reply) × ℕ
  | none => ((none, cache), 4)
  | some (attempt, nextCache) => ((some attempt, nextCache), 5)

theorem oracleAttemptStateCosted_result {Query Reply Attempt : Type*} (cache : OracleCache Query Reply)
    (observation : Option (Attempt × OracleCache Query Reply)) :
    (oracleAttemptStateCosted cache observation).1 = oracleAttemptState cache observation := by
  cases observation with
  | none => rfl
  | some pair => cases pair; rfl

theorem oracleAttemptStateCosted_cost_le {Query Reply Attempt : Type*} (cache : OracleCache Query Reply)
    (observation : Option (Attempt × OracleCache Query Reply)) :
    (oracleAttemptStateCosted cache observation).2 ≤ 5 := by
  cases observation with
  | none => exact Nat.le_succ 4
  | some pair => cases pair; exact le_rfl

/-- Count the literal retry policy using only fixed-size status inspection. -/
def oracleRetryRequestedCosted : Option ProverAttemptResult → Bool × ℕ
  | none => (false, 2)
  | some attempt => match attempt.status with
    | .complete => (false, 4)
    | .failed .retryRandomness => (true, 5)
    | .failed .coincidentOpeningQueries => (false, 5)

theorem oracleRetryRequestedCosted_result (attempt : Option ProverAttemptResult) :
    (oracleRetryRequestedCosted attempt).1 = oracleRetryRequested attempt := by
  cases attempt with
  | none => rfl
  | some attempt =>
    rcases attempt with ⟨proof, received, status⟩
    cases status with
    | complete => rfl
    | failed reason => cases reason <;> rfl

theorem oracleRetryRequestedCosted_cost_le (attempt : Option ProverAttemptResult) :
    (oracleRetryRequestedCosted attempt).2 ≤ 5 := by
  cases attempt with
  | none => exact Nat.le_add_right 2 3
  | some attempt =>
    rcases attempt with ⟨proof, received, status⟩
    cases status with
    | complete => exact Nat.le_succ 4
    | failed reason => cases reason <;> exact le_rfl

end Zcash.Snark.ZeroKnowledge
