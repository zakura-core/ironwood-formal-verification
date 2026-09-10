import Zcash.Snark.ZeroKnowledge.InteractiveTestCost
import Zcash.Snark.ZeroKnowledge.RawTapeTestProgram

/-!
# An operational bounded class for the original interactive PRNG game

Programs contain finite input circuits, the complete interactive prover followed
by a finite view circuit, and Boolean composition. There is no arbitrary host
predicate or supplied whole-prover cost certificate. Materialized inputs and
explicit primitive prices have the same interpretation as in the recorded
retry class. The independent verifier tape contains exactly 22 times 512 bits.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Executable test syntax over the single candidate private tape. -/
inductive InteractiveReductionProgram where
  | raw (test : RawTapeTestProgram)
  | observed (test : RecordedTestProgram)
  | negate (program : InteractiveReductionProgram)
  | both (left right : InteractiveReductionProgram)

/-- Every primitive and stored-input access contributes to the structural counter. -/
def InteractiveReductionProgram.evalCosted (prices : ActionReductionPrices) (data : ActionReductionData)
    (bits : List Bool) (privateWords : List (Fin challengeDigestCard)) : InteractiveReductionProgram → Bool × ℕ
  | .raw program =>
    let auxiliary := copyAuxiliaryWordsCosted prices.read data.auxiliary
    let tested := rawTapeTestCosted program prices.read auxiliary.1 [privateWords]
    (tested.1, auxiliary.2 + tested.2 + 5)
  | .observed program =>
    let tested := interactiveTestCosted prices data program bits privateWords
    (tested.1, tested.2 + 1)
  | .negate program =>
    let tested := program.evalCosted prices data bits privateWords
    (!tested.1, tested.2 + 2)
  | .both left right =>
    let a := left.evalCosted prices data bits privateWords
    let b := right.evalCosted prices data bits privateWords
    (a.1 && b.1, a.2 + b.2 + 3)

/-- Composition adds complete costs; the raw branch also pays for its single-row wrapper. -/
def InteractiveReductionProgram.costBudget (prices : ActionReductionPrices) (data : ActionReductionData)
    (bitLength privateLength : ℕ) : InteractiveReductionProgram → ℕ
  | .raw program => data.auxiliary.length * (prices.read + 2) + 1 + rawTapeTestCostBudget program prices.read + 5
  | .observed program => interactiveTestCostBudget prices data program bitLength privateLength + 1
  | .negate program => program.costBudget prices data bitLength privateLength + 2
  | .both left right => left.costBudget prices data bitLength privateLength + right.costBudget prices data bitLength privateLength + 3

/-- Every program satisfies its derived budget on every private-word and verifier-bit list. -/
theorem InteractiveReductionProgram.evalCosted_cost_le (program : InteractiveReductionProgram)
    (prices : ActionReductionPrices) (data : ActionReductionData) (hdata : data.WellFormed)
    (bits : List Bool) (privateWords : List (Fin challengeDigestCard)) :
    (program.evalCosted prices data bits privateWords).2 ≤ program.costBudget prices data bits.length privateWords.length := by
  induction program with
  | raw test =>
    exact Nat.add_le_add_right (Nat.add_le_add (copyAuxiliaryWordsCosted_cost_le prices.read data.auxiliary)
      (rawTapeTestCosted_cost_le test prices.read (copyAuxiliaryWordsCosted prices.read data.auxiliary).1 [privateWords])) 5
  | observed test => exact Nat.add_le_add_right (interactiveTestCosted_cost_le prices data hdata test bits privateWords) 1
  | negate program ih => exact Nat.add_le_add_right ih 2
  | both left right ihLeft ihRight => exact Nat.add_le_add_right (Nat.add_le_add ihLeft ihRight) 3

/-- The candidate PRNG tape stays fixed while the independent verifier bits range over their exact finite space. -/
noncomputable def InteractiveReductionProgram.kernel (program : InteractiveReductionProgram)
    (prices : ActionReductionPrices) (data : ActionReductionData) : Unit → RawPrivateTape data.inputs.length → PMF Bool :=
  fun _ privateTape => (PMF.uniformOfFintype (Fin (22 * 512) → Bool)).map
    (fun bits => (program.evalCosted prices data (List.ofFn bits) (List.ofFn privateTape)).1)

/-- A time-bounded family defined by executable program syntax and its proved complete budget. -/
def interactiveReductionAdmissible (prices : ActionReductionPrices) (data : ActionReductionData) (timeBound : ℕ) :
    Set (Unit → RawPrivateTape data.inputs.length → PMF Bool) :=
  {kernel | data.WellFormed ∧ ∃ program : InteractiveReductionProgram,
    program.costBudget prices data (22 * 512) (fieldSampleCount data.inputs.length) ≤ timeBound ∧
      kernel = program.kernel prices data}

/-- Every admitted test has actual executable code bounded on all candidate tapes and fair-bit outcomes. -/
theorem interactiveReductionAdmissible_runtime (prices : ActionReductionPrices) (data : ActionReductionData)
    (timeBound : ℕ) (kernel : Unit → RawPrivateTape data.inputs.length → PMF Bool)
    (hmember : kernel ∈ interactiveReductionAdmissible prices data timeBound) :
    ∃ program : InteractiveReductionProgram, kernel = program.kernel prices data ∧
      ∀ (privateTape : RawPrivateTape data.inputs.length) (bits : Fin (22 * 512) → Bool),
        (program.evalCosted prices data (List.ofFn bits) (List.ofFn privateTape)).2 ≤ timeBound := by
  obtain ⟨hdata, program, hbudget, hkernel⟩ := hmember
  refine ⟨program, hkernel, ?_⟩
  intro privateTape bits
  have h := program.evalCosted_cost_le prices data hdata (List.ofFn bits) (List.ofFn privateTape)
  rewrite [List.length_ofFn, List.length_ofFn] at h
  exact h.trans hbudget

end Zcash.Snark.ZeroKnowledge
