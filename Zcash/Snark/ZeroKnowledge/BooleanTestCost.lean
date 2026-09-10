import Zcash.Snark.ZeroKnowledge.ListRoutingCost

/-!
# Finite Boolean test programs with counted wire access

A program has constants, input reads, and NAND gates. Each instruction prepends
one output wire; wire zero is the newest previous wire. Missing wires read false.
This is an executable Boolean-circuit language, with sharing through wire indices,
not an arbitrary host-language predicate packaged with a claimed running time.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The complete instruction set for the finite Boolean test circuit. -/
inductive BooleanTestInstruction (Input : Type*)
  | constant (value : Bool)
  | input (address : Input)
  | nand (left right : ℕ)

/-- A circuit records its instruction stream and the output wire to inspect. -/
structure BooleanTestProgram (Input : Type*) where
  instructions : List (BooleanTestInstruction Input)
  output : ℕ

/-- Mathematical semantics of one instruction, with the same totalized wire reads as execution. -/
def BooleanTestInstruction.eval {Input : Type*} (input : Input → Bool) (wires : List Bool) :
    BooleanTestInstruction Input → Bool
  | .constant value => value
  | .input address => input address
  | .nand left right => !(wires.getD left false && wires.getD right false)

/-- Count every input-reader callback, wire traversal, Boolean operation, and instruction dispatch. -/
def BooleanTestInstruction.evalCosted {Input : Type*} (read : ℕ) (input : Input → Bool × ℕ)
    (wires : List Bool) : BooleanTestInstruction Input → Bool × ℕ
  | .constant value => (value, 1)
  | .input address => let value := input address; (value.1, value.2 + 2)
  | .nand left right =>
    let a := getDListCosted read false wires left
    let b := getDListCosted read false wires right
    (!(a.1 && b.1), a.2 + b.2 + 3)

theorem BooleanTestInstruction.evalCosted_result {Input : Type*} (read : ℕ) (input : Input → Bool × ℕ)
    (wires : List Bool) (instruction : BooleanTestInstruction Input) :
    (instruction.evalCosted read input wires).1 = instruction.eval (fun address => (input address).1) wires := by
  cases instruction <;> simp only [evalCosted, eval, getDListCosted_result]

/-- The ideal circuit retains every computed wire in instruction order. -/
def runBooleanTest {Input : Type*} (input : Input → Bool) :
    List (BooleanTestInstruction Input) → List Bool → List Bool
  | [], wires => wires
  | instruction :: later, wires => runBooleanTest input later (instruction.eval input wires :: wires)

/-- The same circuit execution with all gate and wire-storage costs included. -/
def runBooleanTestCosted {Input : Type*} (read : ℕ) (input : Input → Bool × ℕ) :
    List (BooleanTestInstruction Input) → List Bool → List Bool × ℕ
  | [], wires => (wires, 1)
  | instruction :: later, wires =>
    let value := instruction.evalCosted read input wires
    let rest := runBooleanTestCosted read input later (value.1 :: wires)
    (rest.1, value.2 + rest.2 + 3)

theorem runBooleanTestCosted_result {Input : Type*} (read : ℕ) (input : Input → Bool × ℕ)
    (instructions : List (BooleanTestInstruction Input)) (wires : List Bool) :
    (runBooleanTestCosted read input instructions wires).1 =
      runBooleanTest (fun address => (input address).1) instructions wires := by
  induction instructions generalizing wires with
  | nil => rfl
  | cons instruction later ih =>
    simp only [runBooleanTestCosted, runBooleanTest, ih, BooleanTestInstruction.evalCosted_result]

theorem runBooleanTestCosted_length {Input : Type*} (read : ℕ) (input : Input → Bool × ℕ)
    (instructions : List (BooleanTestInstruction Input)) (wires : List Bool) :
    (runBooleanTestCosted read input instructions wires).1.length = instructions.length + wires.length := by
  induction instructions generalizing wires with
  | nil => simp only [runBooleanTestCosted, List.length_nil, Nat.zero_add]
  | cons instruction later ih =>
    simp only [runBooleanTestCosted, ih, List.length_cons]
    omega

/-- A test's Boolean result, including its selected output wire. -/
def BooleanTestProgram.eval {Input : Type*} (program : BooleanTestProgram Input) (input : Input → Bool) : Bool :=
  (runBooleanTest input program.instructions []).getD program.output false

/-- Execute the circuit and charge the final output-wire read. -/
def BooleanTestProgram.evalCosted {Input : Type*} (program : BooleanTestProgram Input)
    (read : ℕ) (input : Input → Bool × ℕ) : Bool × ℕ :=
  let wires := runBooleanTestCosted read input program.instructions []
  let output := getDListCosted read false wires.1 program.output
  (output.1, wires.2 + output.2 + 2)

theorem BooleanTestProgram.evalCosted_result {Input : Type*} (program : BooleanTestProgram Input)
    (read : ℕ) (input : Input → Bool × ℕ) :
    (program.evalCosted read input).1 = program.eval (fun address => (input address).1) := by
  simp only [evalCosted, eval, getDListCosted_result, runBooleanTestCosted_result]

end Zcash.Snark.ZeroKnowledge
