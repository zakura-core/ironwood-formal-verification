import Zcash.Snark.ZeroKnowledge.OracleProgramming

/-!
# Replaying a bounded sequence of oracle challenge stages

A stage exposes its current report and asks for the next reply only if that
report permits continuation. The independent replay keeps exactly the queried
prefix of the schedule, including the reply that causes a later stop.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common

/-- The finite schedule on a supplied complete reply sequence. -/
def replayOracleSchedule {Query Reply Value : Type*}
    (report : ℕ → Value) (continues : Value → Bool) (query : ℕ → Query) (reply : ℕ → Reply) :
    ℕ → ℕ → Value × List (Query × Reply)
  | 0, index => (report index, [])
  | budget + 1, index =>
    if continues (report index) then
      let rest := replayOracleSchedule report continues query reply budget (index + 1)
      (rest.1, (query index, reply index) :: rest.2)
    else (report index, [])

/-- The recorded queries are an initial segment of the exact indexed schedule. -/
theorem replayOracleSchedule_queries_prefix {Query Reply Value : Type*}
    (report : ℕ → Value) (continues : Value → Bool) (query : ℕ → Query) (reply : ℕ → Reply)
    (budget index : ℕ) :
    (replayOracleSchedule report continues query reply budget index).2 <+:
      (List.range' index budget).map (fun i => (query i, reply i)) := by
  induction budget generalizing index with
  | zero => exact ⟨[], rfl⟩
  | succ budget ih =>
    cases hc : continues (report index) with
    | false => simp [replayOracleSchedule, hc]
    | true =>
      obtain ⟨tail, htail⟩ := ih (index + 1)
      refine ⟨tail, ?_⟩
      simpa only [replayOracleSchedule, hc, if_true, List.range'_succ,
        List.map_cons, List.cons_append] using congrArg (List.cons (query index, reply index)) htail

/-- Stopping early changes no report when stopped reports already equal the final observation. -/
theorem replayOracleSchedule_result {Query Reply Value : Type*}
    (report : ℕ → Value) (continues : Value → Bool) (query : ℕ → Query) (reply : ℕ → Reply)
    (budget index : ℕ) (target : Value) (hfinal : report (index + budget) = target)
    (hstopped : ∀ i, index ≤ i → i < index + budget → continues (report i) = false → report i = target) :
    (replayOracleSchedule report continues query reply budget index).1 = target := by
  induction budget generalizing index with
  | zero => simpa only [replayOracleSchedule, Nat.add_zero] using hfinal
  | succ budget ih =>
    cases hc : continues (report index) with
    | false =>
      simpa only [replayOracleSchedule, hc, Bool.false_eq_true, if_false] using
        hstopped index le_rfl (by omega) hc
    | true =>
      simp only [replayOracleSchedule, hc, if_true]
      apply ih (index + 1)
      · simpa only [Nat.add_assoc, Nat.add_comm 1 budget] using hfinal
      · intro i hi hlimit hstop
        exact hstopped i (by omega) (by omega) hstop

/-- Distinct addresses in the whole schedule remain distinct in the actually queried prefix. -/
theorem replayOracleSchedule_queries_nodup {Query Reply Value : Type*}
    (report : ℕ → Value) (continues : Value → Bool) (query : ℕ → Query) (reply : ℕ → Reply)
    (budget index : ℕ) (hdistinct : ((List.range' index budget).map query).Nodup) :
    ((replayOracleSchedule report continues query reply budget index).2.map Prod.fst).Nodup := by
  have h := (replayOracleSchedule_queries_prefix report continues query reply budget index).map Prod.fst
  simp only [List.map_map, Function.comp_def] at h
  exact h.sublist.nodup hdistinct

/-- Fill unseen replies with a fixed default; only already received positions may be consulted. -/
def oracleHistoryTape {Reply : Type*} (fallback : Reply) (history : List Reply) : ℕ → Reply :=
  fun i => history.getD i fallback

/-- Appending the next actual reply extends agreement by exactly one position. -/
theorem oracleHistoryTape_snoc_agrees {Reply : Type*} (fallback : Reply) (history : List Reply)
    (whole : ℕ → Reply) (hknown : ∀ i < history.length, oracleHistoryTape fallback history i = whole i) :
    ∀ i < (history ++ [whole history.length]).length,
      oracleHistoryTape fallback (history ++ [whole history.length]) i = whole i := by
  intro i hi
  by_cases hbefore : i < history.length
  · simpa only [oracleHistoryTape, List.getD_append _ _ _ _ hbefore] using hknown i hbefore
  · have heq : i = history.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    subst i
    simp only [oracleHistoryTape, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]

/-- A causal online query tree that recomputes only its already determined report and address. -/
def prefixOracleComp {Query Reply Value : Type*}
    (fallback : Reply) (report : (ℕ → Reply) → ℕ → Value) (continues : Value → Bool)
    (query : (ℕ → Reply) → ℕ → Query) : ℕ → List Reply → OracleComp Query Reply Value
  | 0, history => .pure (report (oracleHistoryTape fallback history) history.length)
  | budget + 1, history =>
    let current := report (oracleHistoryTape fallback history) history.length
    if continues current then
      .query (query (oracleHistoryTape fallback history) history.length)
        (fun reply => prefixOracleComp fallback report continues query budget (history ++ [reply]))
    else .pure current

/-- Each remaining stage issues at most one query, with no queries after a stopped report. -/
theorem prefixOracleComp_queryBound {Query Reply Value : Type*}
    (fallback : Reply) (report : (ℕ → Reply) → ℕ → Value) (continues : Value → Bool)
    (query : (ℕ → Reply) → ℕ → Query) (budget : ℕ) (history : List Reply) :
    (prefixOracleComp fallback report continues query budget history).QueryBound budget := by
  induction budget generalizing history with
  | zero => exact .pure _ _
  | succ budget ih =>
    simp only [prefixOracleComp]
    cases continues (report (oracleHistoryTape fallback history) history.length) with
    | false => exact .pure _ _
    | true => exact .query fun reply => ih (history ++ [reply])

/-- Causality connects independent online execution to the fixed complete-tape replay exactly. -/
theorem prefixOracleComp_replay {Query Reply Value : Type*}
    (fallback : Reply) (report : (ℕ → Reply) → ℕ → Value) (continues : Value → Bool)
    (query : (ℕ → Reply) → ℕ → Query)
    (hreport : ∀ n left right, (∀ i < n, left i = right i) → report left n = report right n)
    (hquery : ∀ n left right, (∀ i < n, left i = right i) → query left n = query right n)
    (budget : ℕ) (history : List Reply) (whole : ℕ → Reply)
    (hknown : ∀ i < history.length, oracleHistoryTape fallback history i = whole i) :
    freshOracleRunTape budget (prefixOracleComp fallback report continues query budget history)
        (fun i => whole (history.length + i.val)) =
      some (replayOracleSchedule (report whole) continues (query whole) whole budget history.length) := by
  induction budget generalizing history with
  | zero =>
    simp only [prefixOracleComp, freshOracleRunTape, replayOracleSchedule,
      hreport history.length _ whole hknown]
  | succ budget ih =>
    have hr := hreport history.length _ whole hknown
    have hq := hquery history.length _ whole hknown
    cases hc : continues (report whole history.length) with
    | false => simp only [prefixOracleComp, hr, hc, Bool.false_eq_true, if_false,
        freshOracleRunTape, replayOracleSchedule]
    | true =>
      have htail : Fin.tail (fun i : Fin (budget + 1) => whole (history.length + i.val)) =
          fun i : Fin budget => whole ((history ++ [whole history.length]).length + i.val) := by
        funext i
        simp only [Fin.tail, Fin.val_succ, List.length_append, List.length_singleton,
          Nat.add_assoc, Nat.add_comm 1 i.val]
      simp only [prefixOracleComp, hr, hq, hc, if_true,
        freshOracleRunTape, Fin.val_zero, Nat.add_zero]
      rw [htail, ih (history ++ [whole history.length])
        (oracleHistoryTape_snoc_agrees fallback history whole hknown)]
      simp only [replayOracleSchedule, hc, if_true, Option.map_some,
        List.length_append, List.length_singleton]

end Zcash.Snark.ZeroKnowledge
