import Zcash.Snark.ZeroKnowledge.RecordedTestReadBound
import Zcash.Snark.ZeroKnowledge.BooleanTestBound

namespace Zcash.Snark.ZeroKnowledge

/-- A finite circuit over the complete public view and stored auxiliary words. -/
abbrev RecordedTestProgram := BooleanTestProgram RecordedTestAddress

def recordedViewTest (program : RecordedTestProgram) (auxiliary : List (Fin challengeDigestCard))
    (view : ActionRetryRecordedView) : Bool :=
  program.eval (fun address => address.eval auxiliary view)

def recordedViewTestCosted (program : RecordedTestProgram) (read canonicalRead : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (view : ActionRetryRecordedView) : Bool × ℕ :=
  program.evalCosted read (fun address => address.evalCosted read canonicalRead auxiliary view)

/-- The counted test has exactly the circuit's public-view semantics. -/
theorem recordedViewTestCosted_result (program : RecordedTestProgram) (read canonicalRead : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (view : ActionRetryRecordedView) :
    (recordedViewTestCosted program read canonicalRead auxiliary view).1 = recordedViewTest program auxiliary view := by
  simp only [recordedViewTestCosted, recordedViewTest, BooleanTestProgram.evalCosted_result, RecordedTestAddress.evalCosted_result]

def recordedViewTestCostBudget (program : RecordedTestProgram) (read canonicalRead : ℕ) : ℕ :=
  program.costBudget read (fun address => address.costBudget read canonicalRead)

/-- No arbitrary view-test callback or auxiliary-data read remains unpriced. -/
theorem recordedViewTestCosted_cost_le (program : RecordedTestProgram) (read canonicalRead : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (view : ActionRetryRecordedView) :
    (recordedViewTestCosted program read canonicalRead auxiliary view).2 ≤ recordedViewTestCostBudget program read canonicalRead :=
  program.evalCosted_cost_le read _ _ (fun address => address.evalCosted_cost_le read canonicalRead auxiliary view)

/-- The exhaustion test required by the unlimited seeded-stream reduction is a one-input circuit. -/
def recordedExhaustionTest : RecordedTestProgram := ⟨[.input .exhausted], 0⟩

theorem recordedExhaustionTest_eval (auxiliary : List (Fin challengeDigestCard)) (view : ActionRetryRecordedView) :
    recordedViewTest recordedExhaustionTest auxiliary view = view.1.exhausted := rfl

/-- Copy retained auxiliary input cells explicitly before testing; supplied inputs are stored raw words. -/
def copyAuxiliaryWordsCosted (read : ℕ) (words : List (Fin challengeDigestCard)) : List (Fin challengeDigestCard) × ℕ :=
  mapListCosted (fun word => (word, read + 1)) words

theorem copyAuxiliaryWordsCosted_result (read : ℕ) (words : List (Fin challengeDigestCard)) :
    (copyAuxiliaryWordsCosted read words).1 = words := by
  simp only [copyAuxiliaryWordsCosted, mapListCosted_result]
  exact List.map_id words

theorem copyAuxiliaryWordsCosted_cost_le (read : ℕ) (words : List (Fin challengeDigestCard)) :
    (copyAuxiliaryWordsCosted read words).2 ≤ words.length * (read + 2) + 1 :=
  mapListCosted_cost_le _ _ _ (fun _ _ => le_rfl)

end Zcash.Snark.ZeroKnowledge
