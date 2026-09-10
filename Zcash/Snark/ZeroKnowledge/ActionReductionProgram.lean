import Zcash.Snark.ZeroKnowledge.ObservedReductionCost
import Zcash.Snark.ZeroKnowledge.RawTapeTestProgram

/-!
# A concrete program class for the PRNG security assumption

The class contains ordinary raw-prefix circuits, full real-prover/view circuits,
and Boolean compositions of either. The prover operation below is a fixed macro
expanding to the fully counted source-equivalent implementation. It is not a
caller-supplied function with an assumed price. All programs use stored data,
and every invocation materializes and charges its retained auxiliary words.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Closed executable programs; no constructor accepts an arbitrary host-language computation. -/
inductive ActionReductionProgram
  | raw (test : RawTapeTestProgram)
  | observed (test : RecordedTestProgram)
  | negate (program : ActionReductionProgram)
  | both (left right : ActionReductionProgram)

/-- Execute every operation, retaining its actual structural counter. Both branches share the supplied fair tape. -/
def ActionReductionProgram.evalCosted (prices : ActionReductionPrices) (data : ActionReductionData)
    (budget : ℕ) (bits : List Bool) (privateRows : List (List (Fin challengeDigestCard))) :
    ActionReductionProgram → Bool × ℕ
  | .raw program =>
    let auxiliary := copyAuxiliaryWordsCosted prices.read data.auxiliary
    let tested := rawTapeTestCosted program prices.read auxiliary.1 privateRows
    (tested.1, auxiliary.2 + tested.2 + 3)
  | .observed program =>
    let tested := observedReductionCosted prices data program budget bits privateRows
    (tested.1, tested.2 + 1)
  | .negate program =>
    let tested := program.evalCosted prices data budget bits privateRows
    (!tested.1, tested.2 + 2)
  | .both left right =>
    let a := left.evalCosted prices data budget bits privateRows
    let b := right.evalCosted prices data budget bits privateRows
    (a.1 && b.1, a.2 + b.2 + 3)

/-- The explicit complete budget is additive under program composition. -/
def ActionReductionProgram.costBudget (prices : ActionReductionPrices) (data : ActionReductionData)
    (budget bitLength : ℕ) : ActionReductionProgram → ℕ
  | .raw program => data.auxiliary.length * (prices.read + 2) + 1 + rawTapeTestCostBudget program prices.read + 3
  | .observed program => observedReductionCostBudget prices data program budget bitLength + 1
  | .negate program => program.costBudget prices data budget bitLength + 2
  | .both left right => left.costBudget prices data budget bitLength + right.costBudget prices data budget bitLength + 3

/-- Every complete program is bounded on every stored prefix of the specified shape. -/
theorem ActionReductionProgram.evalCosted_cost_le (program : ActionReductionProgram)
    (prices : ActionReductionPrices) (data : ActionReductionData) (hdata : data.WellFormed)
    (budget : ℕ) (bits : List Bool) (privateRows : List (List (Fin challengeDigestCard)))
    (hlength : privateRows.length = budget)
    (hwidth : ∀ row ∈ privateRows, row.length = fieldSampleCount data.inputs.length) :
    (program.evalCosted prices data budget bits privateRows).2 ≤ program.costBudget prices data budget bits.length := by
  induction program with
  | raw test =>
    have ha := copyAuxiliaryWordsCosted_cost_le prices.read data.auxiliary
    have ht := rawTapeTestCosted_cost_le test prices.read (copyAuxiliaryWordsCosted prices.read data.auxiliary).1 privateRows
    exact Nat.add_le_add_right (Nat.add_le_add ha ht) 3
  | observed test =>
    exact Nat.add_le_add_right (observedReductionCosted_cost_le prices data hdata test budget bits privateRows hlength hwidth) 1
  | negate program ih => exact Nat.add_le_add_right ih 2
  | both left right ihLeft ihRight => exact Nat.add_le_add_right (Nat.add_le_add ihLeft ihRight) 3

/-- Fair verifier bits are a separate fixed-length input; candidate private words are never replaced by fair samples. -/
noncomputable def ActionReductionProgram.kernel (program : ActionReductionProgram) (prices : ActionReductionPrices)
    (data : ActionReductionData) (budget : ℕ) : Unit → RawPrivateRetryTape data.inputs.length budget → PMF Bool :=
  fun _ privateTape => (PMF.uniformOfFintype (Fin ((budget * 22) * 512) → Bool)).map (fun bits =>
    (program.evalCosted prices data budget (List.ofFn bits) (List.ofFn (fun i => List.ofFn (privateTape i)))).1)

/-- Security is assumed for this operationally defined, time-bounded family of programs. -/
def actionReductionAdmissible (prices : ActionReductionPrices) (data : ActionReductionData) (budget timeBound : ℕ) :
    Set (Unit → RawPrivateRetryTape data.inputs.length budget → PMF Bool) :=
  {kernel | data.WellFormed ∧ ∃ program : ActionReductionProgram,
    program.costBudget prices data budget ((budget * 22) * 512) ≤ timeBound ∧ kernel = program.kernel prices data budget}

/-- Membership supplies actual bounded executable code, for all candidate prefixes and fair-bit outcomes. -/
theorem actionReductionAdmissible_runtime (prices : ActionReductionPrices) (data : ActionReductionData)
    (budget timeBound : ℕ) (kernel : Unit → RawPrivateRetryTape data.inputs.length budget → PMF Bool)
    (hmember : kernel ∈ actionReductionAdmissible prices data budget timeBound) :
    ∃ program : ActionReductionProgram, kernel = program.kernel prices data budget ∧
      ∀ (privateTape : RawPrivateRetryTape data.inputs.length budget) (bits : Fin ((budget * 22) * 512) → Bool),
        (program.evalCosted prices data budget (List.ofFn bits) (List.ofFn (fun i => List.ofFn (privateTape i)))).2 ≤ timeBound := by
  obtain ⟨hdata, program, hbudget, hkernel⟩ := hmember
  refine ⟨program, hkernel, ?_⟩
  intro privateTape bits
  have h := program.evalCosted_cost_le prices data hdata budget (List.ofFn bits)
    (List.ofFn (fun i => List.ofFn (privateTape i))) List.length_ofFn (by
      intro row hrow
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
      exact List.length_ofFn)
  rewrite [List.length_ofFn] at h
  exact h.trans hbudget

/-- Larger resource limits preserve every existing member. -/
theorem actionReductionAdmissible_mono (prices : ActionReductionPrices) (data : ActionReductionData)
    (budget left right : ℕ) (hle : left ≤ right) :
    actionReductionAdmissible prices data budget left ⊆ actionReductionAdmissible prices data budget right := by
  rintro kernel ⟨hdata, program, hcost, hkernel⟩
  exact ⟨hdata, program, hcost.trans hle, hkernel⟩

end Zcash.Snark.ZeroKnowledge
