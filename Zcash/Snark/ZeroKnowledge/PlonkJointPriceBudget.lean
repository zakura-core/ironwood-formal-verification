import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorBudget
import Zcash.Snark.ZeroKnowledge.StoredChallengePrices

/-!
# The joint runtime budget depends only on challenge access prices

Challenge values do not enter the cost envelope. This congruence permits the
bit-driven simulator to use its exact, tape-independent positional prices.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Equal access-price records give exactly the same complete algebraic budget. -/
theorem plonkJointSimulatorCostBudget_congr_prices
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess actions baseRead wAccess : ℕ) (key : StoredPlonkKey)
    (left right : Challenges 11 (Fp × ℕ))
    (hprices : Challenges.readPrices left = Challenges.readPrices right) :
    plonkJointSimulatorCostBudget fieldCosts ipaCosts node equal read omegaAccess actions baseRead wAccess key left =
      plonkJointSimulatorCostBudget fieldCosts ipaCosts node equal read omegaAccess actions baseRead wAccess key right := by
  have hx : left.x.2 = right.x.2 := congrArg (fun prices : Challenges 11 ℕ => prices.x) hprices
  have hy : left.y.2 = right.y.2 := congrArg (fun prices : Challenges 11 ℕ => prices.y) hprices
  have hx1 : left.x1.2 = right.x1.2 := congrArg (fun prices : Challenges 11 ℕ => prices.x1) hprices
  have hx2 : left.x2.2 = right.x2.2 := congrArg (fun prices : Challenges 11 ℕ => prices.x2) hprices
  have hx3 : left.x3.2 = right.x3.2 := congrArg (fun prices : Challenges 11 ℕ => prices.x3) hprices
  have hx4 : left.x4.2 = right.x4.2 := congrArg (fun prices : Challenges 11 ℕ => prices.x4) hprices
  simp only [plonkJointSimulatorCostBudget, hx, hy, hx1, hx2, hx3, hx4]

end Zcash.Snark.ZeroKnowledge
