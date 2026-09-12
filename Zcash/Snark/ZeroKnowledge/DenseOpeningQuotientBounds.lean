import Zcash.Snark.ZeroKnowledge.DenseOpeningQuotientCost
import Mathlib.Tactic.GCongr

namespace Zcash.Snark.ZeroKnowledge

/-- Increasing either stored interpolation-list bound preserves the complete coefficient budget. -/
theorem denseLagrangeCoefficientsCostBudget_mono_lengths (costs : FieldOperationCosts)
    (read omegaAccess k : ℕ) {points points' evals evals' : ℕ}
    (hp : points ≤ points') (he : evals ≤ evals') :
    denseLagrangeCoefficientsCostBudget costs read omegaAccess k points evals ≤
      denseLagrangeCoefficientsCostBudget costs read omegaAccess k points' evals' := by
  unfold denseLagrangeCoefficientsCostBudget rowCoefficientCostBudget denseLagrangeNodeCostBudget
    lagrangeEvalCostBudget interpolationWeightCostBudget
  gcongr

/-- The complete opening-quotient budget is monotone in polynomial storage and node count. -/
theorem denseOpeningQuotientCostBudget_mono_lengths (costs : FieldOperationCosts)
    (equal read omegaAccess k : ℕ) {width width' points points' : ℕ}
    (hw : width ≤ width') (hp : points ≤ points') :
    denseOpeningQuotientCostBudget costs equal read omegaAccess k width points ≤
      denseOpeningQuotientCostBudget costs equal read omegaAccess k width' points' := by
  have hi := denseLagrangeCoefficientsCostBudget_mono_lengths costs read omegaAccess k hp hp
  unfold denseOpeningQuotientCostBudget
  gcongr

end Zcash.Snark.ZeroKnowledge
