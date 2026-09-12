import Zcash.Snark.ZeroKnowledge.StreamTestRead
import Zcash.Snark.ZeroKnowledge.BooleanTestMap
import Zcash.Snark.ZeroKnowledge.BooleanTestMeasurable
import Zcash.Snark.ZeroKnowledge.RecordedTestProgram

namespace Zcash.Snark.ZeroKnowledge

/-- Finite circuits can inspect arbitrary selected positions of the complete observed stream. -/
abbrev StreamTestProgram := BooleanTestProgram StreamTestAddress

def streamViewTest (program : StreamTestProgram) (auxiliary : List (Fin challengeDigestCard))
    (stream : ℕ → ActionRetryStreamEntry) : Bool := program.eval (fun address => address.eval auxiliary stream)

/-- Construct the finite-view circuit used by the actual PRNG reduction, preserving all gates and wire indices. -/
def StreamTestProgram.toRecorded (program : StreamTestProgram) : RecordedTestProgram :=
  program.mapInput StreamTestAddress.toRecorded

/-- The stream test's measurability follows from its finite executable syntax, with no external premise. -/
theorem streamViewTest_measurable (program : StreamTestProgram) (auxiliary : List (Fin challengeDigestCard)) :
    Measurable (streamViewTest program auxiliary) :=
  program.eval_measurable _ (fun address => address.eval_measurable auxiliary)

/-- The clipped-view test is exactly the compiled finite circuit on every recorded observation. -/
theorem streamViewTest_recorded (program : StreamTestProgram) (auxiliary : List (Fin challengeDigestCard))
    (view : ActionRetryRecordedView) :
    streamViewTest program auxiliary (fun index => view.1.attempts[index]?) = recordedViewTest program.toRecorded auxiliary view := by
  unfold streamViewTest recordedViewTest StreamTestProgram.toRecorded
  rewrite [BooleanTestProgram.eval_mapInput]
  apply congrArg program.eval
  funext address
  exact address.eval_recorded auxiliary view

end Zcash.Snark.ZeroKnowledge
