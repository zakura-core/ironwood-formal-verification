import Zcash.Snark.ZeroKnowledge.ProtocolCausality

/-!
# Composing causal message stages

Each stage writes its messages and then receives one challenge. The final block
has no further receive. A stage before receive `j` must depend only on the `j`
challenges already received. This interface connects a fixed staged algorithm
to the prefix property used by the actual attempt observer.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Append one receive after each intermediate block, followed by the final response. -/
def protocolStagesTrace {F G : Type*} :
    (rounds : ℕ) → (Fin rounds → List (TranscriptElt F G)) →
      List (TranscriptElt F G) → List (TranscriptElt F G)
  | 0, _, finalResponse => finalResponse
  | rounds + 1, stages, finalResponse =>
      stages 0 ++ .challenge :: protocolStagesTrace rounds (fun j => stages j.succ) finalResponse

/-- The recursive schedule is exactly the concatenation of all message/receive blocks. -/
theorem protocolStagesTrace_eq_flatten {F G : Type*} (rounds : ℕ)
    (stages : Fin rounds → List (TranscriptElt F G)) (finalResponse : List (TranscriptElt F G)) :
    protocolStagesTrace rounds stages finalResponse =
      (List.ofFn (fun j => stages j ++ [.challenge])).flatten ++ finalResponse := by
  induction rounds with
  | zero => simp [protocolStagesTrace]
  | succ rounds ih => simp [protocolStagesTrace, List.ofFn_succ, ih, List.append_assoc]

/-- Message-only blocks contribute exactly one receive apiece. -/
theorem protocolStagesTrace_challengeCount {F G : Type*} (rounds : ℕ)
    (stages : Fin rounds → List (TranscriptElt F G)) (finalResponse : List (TranscriptElt F G))
    (h : ∀ j, protocolChallengeCount (stages j) = 0) :
    protocolChallengeCount (protocolStagesTrace rounds stages finalResponse) =
      rounds + protocolChallengeCount finalResponse := by
  induction rounds with
  | zero => simp [protocolStagesTrace]
  | succ rounds ih =>
    simp only [protocolStagesTrace, protocolChallengeCount_append, h 0, zero_add, protocolChallengeCount]
    rw [ih _ (fun j => h j.succ)]
    omega

/-- Agreement of the stages already due suffices for agreement of the entire observed prefix. -/
theorem protocolStagesTrace_prefix_congr {F G : Type*} (rounds : ℕ) :
    ∀ (left right : Fin rounds → List (TranscriptElt F G))
      (finalLeft finalRight : List (TranscriptElt F G)),
      (∀ j, protocolChallengeCount (left j) = 0) →
      (∀ j, protocolChallengeCount (right j) = 0) → ∀ n : ℕ,
      (∀ j : Fin rounds, j.val ≤ n → left j = right j) →
      (rounds ≤ n → finalLeft = finalRight) →
      protocolPrefix n (protocolStagesTrace rounds left finalLeft) =
        protocolPrefix n (protocolStagesTrace rounds right finalRight) := by
  induction rounds with
  | zero =>
    intro left right finalLeft finalRight _ _ n _ hfinal
    rw [hfinal (by omega)]
    rfl
  | succ rounds ih =>
    intro left right finalLeft finalRight hleft hright n hstage hfinal
    have hl : protocolChallengeCount (left 0) ≤ n := by rw [hleft 0]; exact Nat.zero_le _
    have hr : protocolChallengeCount (right 0) ≤ n := by rw [hright 0]; exact Nat.zero_le _
    simp only [protocolStagesTrace]
    rw [protocolPrefix_append_of_count_le n (left 0) _ hl,
      protocolPrefix_append_of_count_le n (right 0) _ hr]
    simp only [hleft 0, hright 0, Nat.sub_zero]
    rw [hstage 0 (by simp)]
    cases n with
    | zero => rfl
    | succ n =>
      simp only [protocolPrefix]
      rw [ih (fun j => left j.succ) (fun j => right j.succ) finalLeft finalRight
        (fun j => hleft j.succ) (fun j => hright j.succ) n
        (fun j hj => hstage j.succ (by simpa using hj)) (fun hn => hfinal (by omega))]

end Zcash.Snark.ZeroKnowledge
