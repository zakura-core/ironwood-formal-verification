import Zcash.Snark.ZeroKnowledge.BooleanTestCost

namespace Zcash.Snark.ZeroKnowledge

/-- Relabel input ports without changing any gate or wire index. -/
def BooleanTestInstruction.mapInput {Input Output : Type*} (embed : Input → Output) :
    BooleanTestInstruction Input → BooleanTestInstruction Output
  | .constant value => .constant value
  | .input address => .input (embed address)
  | .nand left right => .nand left right

/-- Reindexing an instruction's inputs is equivalent to composing its reader, supporting embeddings
into larger observed views. -/
theorem BooleanTestInstruction.eval_mapInput {Input Output : Type*} (instruction : BooleanTestInstruction Input)
    (embed : Input → Output) (read : Output → Bool) (wires : List Bool) :
    (instruction.mapInput embed).eval read wires = instruction.eval (read ∘ embed) wires := by
  cases instruction <;> rfl

def BooleanTestProgram.mapInput {Input Output : Type*} (program : BooleanTestProgram Input)
    (embed : Input → Output) : BooleanTestProgram Output :=
  ⟨program.instructions.map (BooleanTestInstruction.mapInput embed), program.output⟩

/-- Reindexing every instruction preserves the wire sequence under the composed reader, lifting
input embeddings to programs. -/
theorem runBooleanTest_mapInput {Input Output : Type*} (embed : Input → Output) (read : Output → Bool)
    (instructions : List (BooleanTestInstruction Input)) (wires : List Bool) :
    runBooleanTest read (instructions.map (BooleanTestInstruction.mapInput embed)) wires =
      runBooleanTest (read ∘ embed) instructions wires := by
  induction instructions generalizing wires with
  | nil => rfl
  | cons instruction later ih =>
    simp only [List.map_cons, runBooleanTest, BooleanTestInstruction.eval_mapInput, ih]

/-- Embedding a test's addresses preserves its output under the corresponding reader, allowing one
view test to act on a larger view. -/
theorem BooleanTestProgram.eval_mapInput {Input Output : Type*} (program : BooleanTestProgram Input)
    (embed : Input → Output) (read : Output → Bool) :
    (program.mapInput embed).eval read = program.eval (read ∘ embed) := by
  simp only [eval, mapInput, runBooleanTest_mapInput]

/-- The code translation has exactly the original instruction count. -/
theorem BooleanTestProgram.mapInput_length {Input Output : Type*} (program : BooleanTestProgram Input)
    (embed : Input → Output) : (program.mapInput embed).instructions.length = program.instructions.length := by
  simp only [mapInput, List.length_map]

end Zcash.Snark.ZeroKnowledge
