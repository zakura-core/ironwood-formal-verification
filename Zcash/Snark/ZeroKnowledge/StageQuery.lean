import Zcash.Snark.ZeroKnowledge.ProtocolStages
import Zcash.Snark.ZeroKnowledge.TranscriptQuery

/-!
# Query prefixes of the staged message schedule

The address for receive `j` contains exactly the first `j + 1` message/receive
blocks. The terminal response never enters a challenge address.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The next query terminates exactly the current stage, independently of later messages. -/
theorem protocolStagesTrace_queryPrefix {F G : Type*} (rounds : ℕ) :
    ∀ (stages : Fin rounds → List (TranscriptElt F G)) (finalResponse : List (TranscriptElt F G)),
      (∀ j, protocolChallengeCount (stages j) = 0) → ∀ index : Fin rounds,
      protocolPrefix index.val (protocolStagesTrace rounds stages finalResponse) ++ [.challenge] =
        ((List.ofFn (fun j => stages j ++ [.challenge])).take (index.val + 1)).flatten := by
  induction rounds with
  | zero => intro _ _ _ index; exact Fin.elim0 index
  | succ rounds ih =>
    intro stages finalResponse hstage index
    refine Fin.cases ?_ (fun j => ?_) index
    · simp only [Fin.val_zero, protocolStagesTrace, List.ofFn_succ]
      rw [protocolPrefix_append_of_count_le 0 (stages 0) _ (by rw [hstage 0])]
      simp [hstage, protocolPrefix]
    · simp only [Fin.val_succ, protocolStagesTrace, List.ofFn_succ]
      rw [protocolPrefix_append_of_count_le (j.val + 1) (stages 0) _ (by rw [hstage 0]; omega)]
      simp only [hstage 0, Nat.sub_zero, protocolPrefix, List.take_succ_cons,
        List.flatten_cons, List.append_assoc, List.cons_append]
      rw [ih (fun i => stages i.succ) finalResponse (fun i => hstage i.succ) j]
      simp only [List.nil_append]

/-- Public initialization is prepended to precisely the scheduled query blocks. -/
theorem protocolQueryPrefix_stages {F G : Type*} (rounds : ℕ)
    (initial : List (TranscriptElt F G)) (stages : Fin rounds → List (TranscriptElt F G))
    (finalResponse : List (TranscriptElt F G)) (hstage : ∀ j, protocolChallengeCount (stages j) = 0)
    (index : Fin rounds) :
    protocolQueryPrefix initial (protocolStagesTrace rounds stages finalResponse) index.val =
      initial ++ ((List.ofFn (fun j => stages j ++ [.challenge])).take (index.val + 1)).flatten := by
  rw [protocolQueryPrefix, List.append_assoc, protocolStagesTrace_queryPrefix rounds stages finalResponse hstage index]

end Zcash.Snark.ZeroKnowledge
