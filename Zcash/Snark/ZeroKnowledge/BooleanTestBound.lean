import Zcash.Snark.ZeroKnowledge.BooleanTestCost

namespace Zcash.Snark.ZeroKnowledge

/-- Only an input instruction invokes an external reader; its full certified cost is retained. -/
def BooleanTestInstruction.inputCost {Input : Type*} (price : Input → ℕ) : BooleanTestInstruction Input → ℕ
  | .input address => price address
  | _ => 0

theorem BooleanTestInstruction.evalCosted_cost_le {Input : Type*} (read : ℕ)
    (input : Input → Bool × ℕ) (price : Input → ℕ) (hinput : ∀ address, (input address).2 ≤ price address)
    (wires : List Bool) (cap : ℕ) (hcap : wires.length ≤ cap) (instruction : BooleanTestInstruction Input) :
    (instruction.evalCosted read input wires).2 ≤ instruction.inputCost price + 4 * cap + 2 * read + 5 := by
  cases instruction with
  | constant value => simp only [evalCosted, inputCost]; omega
  | input address => have h := hinput address; simp only [evalCosted, inputCost]; omega
  | nand left right =>
    have hl := getDListCosted_cost_le read false wires left
    have hr := getDListCosted_cost_le read false wires right
    simp only [evalCosted, inputCost]
    omega

/-- Running a finite circuit pays for every gate, input read, and the growing stored wire list. -/
theorem runBooleanTestCosted_cost_le {Input : Type*} (read : ℕ) (input : Input → Bool × ℕ)
    (price : Input → ℕ) (hinput : ∀ address, (input address).2 ≤ price address)
    (instructions : List (BooleanTestInstruction Input)) (wires : List Bool) (cap : ℕ)
    (hcap : wires.length + instructions.length ≤ cap) :
    (runBooleanTestCosted read input instructions wires).2 ≤
      (instructions.map (BooleanTestInstruction.inputCost price)).sum +
        instructions.length * (4 * cap + 2 * read + 8) + 1 := by
  induction instructions generalizing wires with
  | nil => simp only [runBooleanTestCosted, List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons instruction later ih =>
    have hs : wires.length ≤ cap := le_trans (Nat.le_add_right _ _) hcap
    have hv := instruction.evalCosted_cost_le read input price hinput wires cap hs
    have hn : ((instruction.evalCosted read input wires).1 :: wires).length + later.length ≤ cap := by
      simp only [List.length_cons] at hcap ⊢
      omega
    have hi := ih ((instruction.evalCosted read input wires).1 :: wires) hn
    simp only [runBooleanTestCosted, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- An explicit polynomial envelope in the circuit length and the sum of input-access budgets. -/
def BooleanTestProgram.costBudget {Input : Type*} (program : BooleanTestProgram Input)
    (read : ℕ) (price : Input → ℕ) : ℕ :=
  (program.instructions.map (BooleanTestInstruction.inputCost price)).sum +
    program.instructions.length * (4 * program.instructions.length + 2 * read + 8) +
    2 * program.instructions.length + read + 4

theorem BooleanTestProgram.evalCosted_cost_le {Input : Type*} (program : BooleanTestProgram Input)
    (read : ℕ) (input : Input → Bool × ℕ) (price : Input → ℕ)
    (hinput : ∀ address, (input address).2 ≤ price address) :
    (program.evalCosted read input).2 ≤ program.costBudget read price := by
  have hr := runBooleanTestCosted_cost_le read input price hinput program.instructions [] program.instructions.length (by simp)
  have hl := runBooleanTestCosted_length read input program.instructions []
  have ho := getDListCosted_cost_le read false (runBooleanTestCosted read input program.instructions []).1 program.output
  rewrite [hl] at ho
  unfold evalCosted costBudget
  dsimp only
  simp only [List.length_nil, Nat.add_zero] at ho
  omega

end Zcash.Snark.ZeroKnowledge
