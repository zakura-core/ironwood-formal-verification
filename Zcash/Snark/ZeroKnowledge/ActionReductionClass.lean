import Zcash.Snark.ZeroKnowledge.ActionReductionProgram

namespace Zcash.Snark.ZeroKnowledge

/-- A one-instruction ordinary raw-tape program that returns its literal Boolean value. -/
def ActionReductionProgram.constant (value : Bool) : ActionReductionProgram := .raw ⟨[.constant value], 0⟩

theorem ActionReductionProgram.kernel_constant (value : Bool) (prices : ActionReductionPrices)
    (data : ActionReductionData) (budget : ℕ) :
    (constant value).kernel prices data budget = fun _ _ => PMF.pure value := by
  funext token privateTape
  unfold kernel
  dsimp only [constant, evalCosted]
  simp only [rawTapeTestCosted_result]
  change (PMF.uniformOfFintype (Fin ((budget * 22) * 512) → Bool)).map (fun _ => value) = PMF.pure value
  exact PMF.map_const _ _

theorem ActionReductionProgram.constant_costBudget (value : Bool) (prices : ActionReductionPrices)
    (data : ActionReductionData) (budget bitLength : ℕ) :
    (constant value).costBudget prices data budget bitLength =
      data.auxiliary.length * (prices.read + 2) + 3 * prices.read + 22 := by
  unfold constant costBudget rawTapeTestCostBudget BooleanTestProgram.costBudget
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, BooleanTestInstruction.inputCost,
    List.length_cons, List.length_nil]
  omega

/-- The admissible family contains both constant outcomes as well as arbitrary raw and observed circuits. -/
theorem actionReductionAdmissible_constants (prices : ActionReductionPrices) (data : ActionReductionData)
    (hdata : data.WellFormed) (budget timeBound : ℕ)
    (hbound : data.auxiliary.length * (prices.read + 2) + 3 * prices.read + 22 ≤ timeBound) (value : Bool) :
    (fun _ _ => PMF.pure value) ∈ actionReductionAdmissible prices data budget timeBound := by
  refine ⟨hdata, .constant value, ?_, ?_⟩
  · exact (ActionReductionProgram.constant_costBudget value prices data budget _).le.trans hbound
  · exact (ActionReductionProgram.kernel_constant value prices data budget).symm

/-- Negation runs the same program on the same coins and flips only its returned bit. -/
theorem ActionReductionProgram.kernel_negate (program : ActionReductionProgram) (prices : ActionReductionPrices)
    (data : ActionReductionData) (budget : ℕ) :
    (negate program).kernel prices data budget = fun token privateTape =>
      (program.kernel prices data budget token privateTape).map Bool.not := by
  funext token privateTape
  simp only [kernel, evalCosted, PMF.map_comp, Function.comp_def]

end Zcash.Snark.ZeroKnowledge
