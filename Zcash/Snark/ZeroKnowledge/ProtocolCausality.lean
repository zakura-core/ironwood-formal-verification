import Zcash.Snark.ZeroKnowledge.ProverAttempt

/-!
# Causality of a transcript computed from a complete challenge tape

The prefix after `n` receives includes every message before the next receive.
Causality means that changing later challenges cannot change this prefix. The
observer respects that property, including point failures and post-challenge
errors, when its checks also use only challenges already received.

This is a deterministic property of the specified algorithms. It requires no
uniformity, nonzero challenges, successful emission, or verifier acceptance.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Keep the messages up to, but not including, the next receive after the given budget. -/
def protocolPrefix {F G : Type*} : ℕ → List (TranscriptElt F G) → List (TranscriptElt F G)
  | _, [] => []
  | 0, .challenge :: _ => []
  | n + 1, .challenge :: rest => .challenge :: protocolPrefix n rest
  | n, .point point :: rest => .point point :: protocolPrefix n rest
  | n, .scalar scalar :: rest => .scalar scalar :: protocolPrefix n rest

/-- Truncation preserves order and never invents a message. -/
theorem protocolPrefix_isPrefix {F G : Type*} (n : ℕ) (trace : List (TranscriptElt F G)) :
    protocolPrefix n trace <+: trace := by
  induction trace generalizing n with
  | nil => exact ⟨[], rfl⟩
  | cons elt trace ih =>
    cases elt with
    | point point =>
      obtain ⟨later, h⟩ := ih n
      exact ⟨later, by simpa only [protocolPrefix, List.cons_append, List.cons.injEq, true_and] using h⟩
    | scalar scalar =>
      obtain ⟨later, h⟩ := ih n
      exact ⟨later, by simpa only [protocolPrefix, List.cons_append, List.cons.injEq, true_and] using h⟩
    | challenge =>
      cases n with
      | zero => exact ⟨.challenge :: trace, rfl⟩
      | succ n =>
        obtain ⟨later, h⟩ := ih n
        exact ⟨later, by simpa only [protocolPrefix, List.cons_append, List.cons.injEq, true_and] using h⟩

/-- The truncated schedule reads exactly the smaller of the budget and the original count. -/
theorem protocolPrefix_challengeCount {F G : Type*} (n : ℕ) (trace : List (TranscriptElt F G)) :
    protocolChallengeCount (protocolPrefix n trace) = min n (protocolChallengeCount trace) := by
  induction trace generalizing n with
  | nil => simp [protocolPrefix, protocolChallengeCount]
  | cons elt trace ih =>
    cases elt with
    | point point => exact ih n
    | scalar scalar => exact ih n
    | challenge =>
      cases n <;> simp [protocolPrefix, protocolChallengeCount, ih]
      omega

/-- Enough received challenges expose the complete message schedule. -/
theorem protocolPrefix_eq_of_count_le {F G : Type*} (n : ℕ)
    (trace : List (TranscriptElt F G)) (h : protocolChallengeCount trace ≤ n) :
    protocolPrefix n trace = trace := by
  induction trace generalizing n with
  | nil => rfl
  | cons elt trace ih =>
    cases elt with
    | point point => simp only [protocolPrefix, ih n h]
    | scalar scalar => simp only [protocolPrefix, ih n h]
    | challenge =>
      cases n with
      | zero => simp [protocolChallengeCount] at h
      | succ n =>
        have ht : protocolChallengeCount trace ≤ n := by
          simp only [protocolChallengeCount] at h
          omega
        simp only [protocolPrefix, ih n ht]

/-- Once an initial stage fits, the remaining budget is used by the following stages. -/
theorem protocolPrefix_append_of_count_le {F G : Type*} (n : ℕ)
    (left right : List (TranscriptElt F G)) (h : protocolChallengeCount left ≤ n) :
    protocolPrefix n (left ++ right) =
      left ++ protocolPrefix (n - protocolChallengeCount left) right := by
  induction left generalizing n with
  | nil => simp [protocolChallengeCount]
  | cons elt left ih =>
    cases elt with
    | point point => simpa only [List.cons_append, protocolPrefix] using congrArg (List.cons (.point point)) (ih n h)
    | scalar scalar => simpa only [List.cons_append, protocolPrefix] using congrArg (List.cons (.scalar scalar)) (ih n h)
    | challenge =>
      cases n with
      | zero => simp [protocolChallengeCount] at h
      | succ n =>
        have ht : protocolChallengeCount left ≤ n := by
          simp only [protocolChallengeCount] at h
          omega
        have hsub : n + 1 - (1 + protocolChallengeCount left) = n - protocolChallengeCount left := by omega
        simpa only [List.cons_append, protocolPrefix, protocolChallengeCount, hsub] using
          congrArg (List.cons .challenge) (ih n ht)

/-- If the next receive is in the initial stage, later stages cannot enter the prefix. -/
theorem protocolPrefix_append_of_lt_count {F G : Type*} (n : ℕ)
    (left right : List (TranscriptElt F G)) (h : n < protocolChallengeCount left) :
    protocolPrefix n (left ++ right) = protocolPrefix n left := by
  induction left generalizing n with
  | nil => simp [protocolChallengeCount] at h
  | cons elt left ih =>
    cases elt with
    | point point => simpa only [List.cons_append, protocolPrefix] using congrArg (List.cons (.point point)) (ih n h)
    | scalar scalar => simpa only [List.cons_append, protocolPrefix] using congrArg (List.cons (.scalar scalar)) (ih n h)
    | challenge =>
      cases n with
      | zero => rfl
      | succ n =>
        have ht : n < protocolChallengeCount left := by
          simp only [protocolChallengeCount] at h
          omega
        simpa only [List.cons_append, protocolPrefix] using congrArg (List.cons .challenge) (ih n ht)

/-- The interpreter never consults challenges or checks beyond its scheduled receives. -/
theorem observeProtocolTrace_congr_challenges {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (left right : ℕ → Fp) (checkLeft checkRight : ℕ → Option ProverAttemptFailure)
    (next : ℕ) (trace : List (TranscriptElt Fp G))
    (hcoins : ∀ j < protocolChallengeCount trace, left (next + j) = right (next + j))
    (hchecks : ∀ j < protocolChallengeCount trace, checkLeft (next + j) = checkRight (next + j)) :
    observeProtocolTrace pointCodec scalarCodec left checkLeft next trace =
      observeProtocolTrace pointCodec scalarCodec right checkRight next trace := by
  induction trace generalizing next with
  | nil => rfl
  | cons elt trace ih =>
    cases elt with
    | point point =>
      cases hp : pointCodec point <;> simp only [observeProtocolTrace, hp]
      rw [ih next hcoins hchecks]
    | scalar scalar =>
      simp only [observeProtocolTrace]
      rw [ih next hcoins hchecks]
    | challenge =>
      have hc : left next = right next := by
        simpa using hcoins 0 (by simp [protocolChallengeCount])
      have he : checkLeft next = checkRight next := by
        simpa using hchecks 0 (by simp [protocolChallengeCount])
      cases hr : checkRight next with
      | some reason => simp only [observeProtocolTrace, he, hr, hc]
      | none =>
        simp only [observeProtocolTrace, he, hr, hc]
        rw [ih (next + 1)]
        · intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            hcoins (j + 1) (by simp only [protocolChallengeCount]; omega)
        · intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            hchecks (j + 1) (by simp only [protocolChallengeCount]; omega)

/-- Future challenge choices cannot change any message already due from the prover. -/
def ProtocolCausal {C G : Type*} (coins : C → ℕ → Fp)
    (trace : C → List (TranscriptElt Fp G)) : Prop :=
  ∀ n left right, (∀ i < n, coins left i = coins right i) →
    protocolPrefix n (trace left) = protocolPrefix n (trace right)

/-- A post-receive check may use the current challenge and every earlier one. -/
def ProtocolChecksCausal {C : Type*} (coins : C → ℕ → Fp)
    (check : C → ℕ → Option ProverAttemptFailure) : Prop :=
  ∀ left right i, (∀ j ≤ i, coins left j = coins right j) → check left i = check right i

/-- Causal messages and checks give identical encoded prefixes before any unseen challenge. -/
theorem protocolCausal_observation {C G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (coins : C → ℕ → Fp) (check : C → ℕ → Option ProverAttemptFailure)
    (trace : C → List (TranscriptElt Fp G))
    (htrace : ProtocolCausal coins trace) (hcheck : ProtocolChecksCausal coins check)
    (n : ℕ) (left right : C) (hcoins : ∀ i < n, coins left i = coins right i) :
    observeProtocolTrace pointCodec scalarCodec (coins left) (check left) 0
        (protocolPrefix n (trace left)) =
      observeProtocolTrace pointCodec scalarCodec (coins right) (check right) 0
        (protocolPrefix n (trace right)) := by
  rw [htrace n left right hcoins]
  apply observeProtocolTrace_congr_challenges
  · intro j hj
    simp only [Nat.zero_add]
    exact hcoins j (hj.trans_le (by rw [protocolPrefix_challengeCount]; exact min_le_left _ _))
  · intro j hj
    simp only [Nat.zero_add]
    apply hcheck left right j
    intro i hi
    apply hcoins i
    exact hi.trans_lt (hj.trans_le (by rw [protocolPrefix_challengeCount]; exact min_le_left _ _))

end Zcash.Snark.ZeroKnowledge
