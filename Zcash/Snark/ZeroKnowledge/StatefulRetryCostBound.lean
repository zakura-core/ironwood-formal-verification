import Zcash.Snark.ZeroKnowledge.StatefulRetryCost

namespace Zcash.Snark.ZeroKnowledge

/-- A per-attempt envelope prices the whole retained history, including the final exhaustion branch.
The state-size invariant accounts for growth across attempts; it is a proof invariant, not an
unpriced operation performed by the runner. -/
theorem runStatefulRetriesCosted_cost_le {A State Tape : Type*}
    (run : State → Tape → (A × State) × ℕ) (retry : A → Bool × ℕ)
    (size : State → ℕ) (valid : Tape → Prop)
    (growth cap runPrice checkPrice : ℕ)
    (hrun : ∀ state, size state ≤ cap → ∀ tape, valid tape → (run state tape).2 ≤ runPrice)
    (hgrowth : ∀ state tape, valid tape → size (run state tape).1.2 ≤ size state + growth)
    (hcheck : ∀ attempt, (retry attempt).2 ≤ checkPrice)
    (tapes : List Tape) (state : State)
    (hvalid : ∀ tape ∈ tapes, valid tape)
    (hsize : size state + growth * tapes.length ≤ cap) :
    (runStatefulRetriesCosted run retry tapes state).2 ≤
      (tapes.length + 1) * (runPrice + checkPrice + 12) := by
  induction tapes generalizing state with
  | nil => simp only [runStatefulRetriesCosted, List.length_nil, Nat.zero_add, Nat.one_mul]; omega
  | cons tape later ih =>
    have ht := hvalid tape List.mem_cons_self
    have hlater : ∀ t ∈ later, valid t := fun t h => hvalid t (List.mem_cons_of_mem _ h)
    have hs : size state ≤ cap := by
      exact le_trans (Nat.le_add_right _ _) hsize
    have hr := hrun state hs tape ht
    have hc := hcheck (run state tape).1.1
    have hg := hgrowth state tape ht
    have hn : size (run state tape).1.2 + growth * later.length ≤ cap := by
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hsize
      omega
    have hi := ih (run state tape).1.2 hlater hn
    let step := runPrice + checkPrice + 12
    simp only [runStatefulRetriesCosted, List.length_cons]
    split
    · change _ ≤ (later.length + 1 + 1) * step
      change _ ≤ (later.length + 1) * step at hi
      rewrite [Nat.add_mul, Nat.one_mul]
      dsimp only [step] at *
      omega
    · have hnonempty : 1 ≤ later.length + 1 + 1 := by omega
      have hstep : step ≤ (later.length + 1 + 1) * step := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right step hnonempty
      exact le_trans (by dsimp only [step]; omega) hstep

end Zcash.Snark.ZeroKnowledge
