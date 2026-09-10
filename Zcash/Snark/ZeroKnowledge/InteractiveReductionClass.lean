import Zcash.Snark.ZeroKnowledge.InteractiveReductionProgram

namespace Zcash.Snark.ZeroKnowledge

/-- A one-instruction ordinary raw-tape program that returns its literal Boolean value. -/
def InteractiveReductionProgram.constant (value : Bool) : InteractiveReductionProgram := .raw ⟨[.constant value], 0⟩

/-- A constant interactive reduction returns its fixed bit on every tape, witnessing a simple member
of the operational test class. -/
theorem InteractiveReductionProgram.kernel_constant (value : Bool) (prices : ActionReductionPrices)
    (data : ActionReductionData) :
    (constant value).kernel prices data = fun _ _ => PMF.pure value := by
  funext token privateTape
  unfold kernel
  dsimp only [constant, evalCosted]
  simp only [rawTapeTestCosted_result]
  change (PMF.uniformOfFintype (Fin (22 * 512) → Bool)).map (fun _ => value) = PMF.pure value
  exact PMF.map_const _ _

/-- The constant interactive reduction charges auxiliary copying and fixed overhead, establishing
its admissibility budget. -/
theorem InteractiveReductionProgram.constant_costBudget (value : Bool) (prices : ActionReductionPrices)
    (data : ActionReductionData) (bitLength privateLength : ℕ) :
    (constant value).costBudget prices data bitLength privateLength =
      data.auxiliary.length * (prices.read + 2) + 3 * prices.read + 24 := by
  unfold constant costBudget rawTapeTestCostBudget BooleanTestProgram.costBudget
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, BooleanTestInstruction.inputCost,
    List.length_cons, List.length_nil]
  omega

/-- The admissible family contains both constant outcomes as well as arbitrary raw and observed circuits. -/
theorem interactiveReductionAdmissible_constants (prices : ActionReductionPrices) (data : ActionReductionData)
    (hdata : data.WellFormed) (timeBound : ℕ)
    (hbound : data.auxiliary.length * (prices.read + 2) + 3 * prices.read + 24 ≤ timeBound) (value : Bool) :
    (fun _ _ => PMF.pure value) ∈ interactiveReductionAdmissible prices data timeBound := by
  refine ⟨hdata, .constant value, ?_, ?_⟩
  · exact (InteractiveReductionProgram.constant_costBudget value prices data _ _).le.trans hbound
  · exact (InteractiveReductionProgram.kernel_constant value prices data).symm

/-- Negation runs the same program on the same coins and flips only its returned bit. -/
theorem InteractiveReductionProgram.kernel_negate (program : InteractiveReductionProgram) (prices : ActionReductionPrices)
    (data : ActionReductionData) :
    (negate program).kernel prices data = fun token privateTape =>
      (program.kernel prices data token privateTape).map Bool.not := by
  funext token privateTape
  simp only [kernel, evalCosted, PMF.map_comp, Function.comp_def]

end Zcash.Snark.ZeroKnowledge
