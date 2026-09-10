import Zcash.Snark.ZeroKnowledge.ProverAttempt

/-!
# An external caller policy for the auxiliary composition theorems

This policy deliberately starts another invocation after a point-encoding
failure or a handled zero-IPA panic. It is an additional caller operation,
absent from the released Orchard proof call and its Zakura model.
The prover's own status contains only completion and terminal failure reasons.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The auxiliary caller chooses to repeat two terminal failures; the prover does not request it. -/
def callerRetryAfterFailure : ProverAttemptStatus → Bool
  | .failed .identityPoint => true
  | .failed .zeroIpaChallenge => true
  | _ => false

/-- A completed proof ends the auxiliary caller's composition. -/
@[simp] theorem callerRetryAfterFailure_complete : callerRetryAfterFailure .complete = false := rfl

/-- The auxiliary caller treats duplicate opening queries as terminal. -/
@[simp] theorem callerRetryAfterFailure_coincident :
    callerRetryAfterFailure (.failed .coincidentOpeningQueries) = false := rfl

/-- Every additional invocation selected by this caller follows a failed attempt. -/
theorem callerRetryAfterFailure_ne_complete (status : ProverAttemptStatus)
    (h : callerRetryAfterFailure status = true) : status ≠ .complete := by
  intro hcomplete
  rw [hcomplete, callerRetryAfterFailure_complete] at h
  cases h

end Zcash.Snark.ZeroKnowledge
