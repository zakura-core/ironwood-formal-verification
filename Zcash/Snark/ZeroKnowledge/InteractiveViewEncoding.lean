import Zcash.Snark.ZeroKnowledge.InteractiveViewCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- The test representation loses neither the observed attempt nor any of the verifier's full tape. -/
theorem interactiveRecordedView_injective : Function.Injective interactiveRecordedView := by
  intro left right h
  have ha := congrArg (fun view : ActionRetryRecordedView => (view.1.attempts.getD 0 (none, [])).1) h
  change some left.2 = some right.2 at ha
  have hs := congrArg (fun view : ActionRetryRecordedView =>
    ((view.1.attempts.getD 1 (none, [])).1.getD ⟨[], [], .complete⟩).received) h
  change plonkChallengeSequence left.1 = plonkChallengeSequence right.1 at hs
  apply Prod.ext
  · apply plonkAttemptChallenge_prefix_injective
    intro index _
    exact congrArg (fun sequence : List Fp => sequence.getD index 0) hs
  · exact Option.some.inj ha

end Zcash.Snark.ZeroKnowledge
