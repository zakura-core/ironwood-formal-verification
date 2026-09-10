import Zcash.Snark.ZeroKnowledge.RecordedTestProgram

namespace Zcash.Snark.ZeroKnowledge

/-- Ordinary PRNG adversary instructions can inspect the candidate prefix directly, or retained auxiliary words. -/
inductive RawTapeTestAddress
  | rowPresent (row : ℕ)
  | word (row column : ℕ) (bit : Option (Fin 512))
  | auxiliary (word : ℕ) (bit : Option (Fin 512))

def RawTapeTestAddress.eval (address : RawTapeTestAddress) (auxiliary : List (Fin challengeDigestCard))
    (rows : List (List (Fin challengeDigestCard))) : Bool :=
  match address with
  | .rowPresent row => rows[row]?.isSome
  | .word row column bit => optionalRawWordTest (rows.getD row [])[column]? bit
  | .auxiliary index bit => optionalRawWordTest auxiliary[index]? bit

def RawTapeTestAddress.evalCosted (address : RawTapeTestAddress) (read : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (rows : List (List (Fin challengeDigestCard))) : Bool × ℕ :=
  match address with
  | .rowPresent row => let value := getOptionListCosted read rows row; (value.1.isSome, value.2 + 2)
  | .word row column bit =>
    let stored := getDListCosted read [] rows row
    let value := getOptionListCosted read stored.1 column
    (optionalRawWordTest value.1 bit, stored.2 + value.2 + 4)
  | .auxiliary index bit => let value := getOptionListCosted read auxiliary index; (optionalRawWordTest value.1 bit, value.2 + 4)

theorem RawTapeTestAddress.evalCosted_result (address : RawTapeTestAddress) (read : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (rows : List (List (Fin challengeDigestCard))) :
    (address.evalCosted read auxiliary rows).1 = address.eval auxiliary rows := by
  cases address <;> simp only [evalCosted, eval, getDListCosted_result, getOptionListCosted_result]

def RawTapeTestAddress.costBudget (address : RawTapeTestAddress) (read : ℕ) : ℕ :=
  let indices := match address with
    | .rowPresent row => row
    | .word row column _ => row + column
    | .auxiliary index _ => index
  2 * indices + 2 * read + 16

theorem RawTapeTestAddress.evalCosted_cost_le (address : RawTapeTestAddress) (read : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (rows : List (List (Fin challengeDigestCard))) :
    (address.evalCosted read auxiliary rows).2 ≤ address.costBudget read := by
  cases address with
  | rowPresent row =>
    have h := getOptionListCosted_cost_le read rows row
    dsimp only [evalCosted, costBudget]
    omega
  | word row column bit =>
    have hr := getDListCosted_cost_le_index read [] rows row
    have hc := getOptionListCosted_cost_le read (getDListCosted read [] rows row).1 column
    dsimp only [evalCosted, costBudget]
    omega
  | auxiliary index bit =>
    have h := getOptionListCosted_cost_le read auxiliary index
    dsimp only [evalCosted, costBudget]
    omega

abbrev RawTapeTestProgram := BooleanTestProgram RawTapeTestAddress

def rawTapeTest (program : RawTapeTestProgram) (auxiliary : List (Fin challengeDigestCard))
    (rows : List (List (Fin challengeDigestCard))) : Bool := program.eval (fun address => address.eval auxiliary rows)

def rawTapeTestCosted (program : RawTapeTestProgram) (read : ℕ) (auxiliary : List (Fin challengeDigestCard))
    (rows : List (List (Fin challengeDigestCard))) : Bool × ℕ :=
  program.evalCosted read (fun address => address.evalCosted read auxiliary rows)

theorem rawTapeTestCosted_result (program : RawTapeTestProgram) (read : ℕ) (auxiliary : List (Fin challengeDigestCard))
    (rows : List (List (Fin challengeDigestCard))) :
    (rawTapeTestCosted program read auxiliary rows).1 = rawTapeTest program auxiliary rows := by
  simp only [rawTapeTestCosted, rawTapeTest, BooleanTestProgram.evalCosted_result, RawTapeTestAddress.evalCosted_result]

def rawTapeTestCostBudget (program : RawTapeTestProgram) (read : ℕ) : ℕ :=
  program.costBudget read (fun address => address.costBudget read)

theorem rawTapeTestCosted_cost_le (program : RawTapeTestProgram) (read : ℕ) (auxiliary : List (Fin challengeDigestCard))
    (rows : List (List (Fin challengeDigestCard))) :
    (rawTapeTestCosted program read auxiliary rows).2 ≤ rawTapeTestCostBudget program read :=
  program.evalCosted_cost_le read _ _ (fun address => address.evalCosted_cost_le read auxiliary rows)

end Zcash.Snark.ZeroKnowledge
