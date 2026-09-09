import Zcash.Snark.ZeroKnowledge.PermutationRowProductCostBound

namespace Zcash.Snark.ZeroKnowledge

/-- Increasing materialized-pair sizes and power limits preserves the complete numerator budget. -/
theorem permutationRowNumeratorCostBudget_mono (costs : FieldOperationCosts)
    (read betaRead gammaRead omegaRead deltaRead chunkLen : ℕ)
    {pairsCost pairsBound count countBound chunk chunkBound row rowBound : ℕ}
    (hp : pairsCost ≤ pairsBound) (hc : count ≤ countBound)
    (hk : chunk ≤ chunkBound) (hr : row ≤ rowBound) :
    permutationRowNumeratorCostBudget costs read pairsCost count betaRead gammaRead omegaRead deltaRead
      chunkLen chunk row ≤
      permutationRowNumeratorCostBudget costs read pairsBound countBound betaRead gammaRead omegaRead deltaRead
        chunkLen chunkBound rowBound := by
  dsimp only [permutationRowNumeratorCostBudget]
  gcongr

/-- Increasing pair preparation and stored-list size preserves the complete denominator budget. -/
theorem permutationRowDenominatorCostBudget_mono (costs : FieldOperationCosts)
    (read betaRead gammaRead : ℕ) {pairsCost pairsBound count countBound : ℕ}
    (hp : pairsCost ≤ pairsBound) (hc : count ≤ countBound) :
    permutationRowDenominatorCostBudget costs read pairsCost count betaRead gammaRead ≤
      permutationRowDenominatorCostBudget costs read pairsBound countBound betaRead gammaRead := by
  dsimp only [permutationRowDenominatorCostBudget]
  gcongr

end Zcash.Snark.ZeroKnowledge
