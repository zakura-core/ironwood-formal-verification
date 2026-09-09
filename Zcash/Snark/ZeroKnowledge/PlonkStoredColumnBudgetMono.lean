import Zcash.Snark.ZeroKnowledge.PlonkStoredColumnCost

namespace Zcash.Snark.ZeroKnowledge

/-- A bound using the final column count covers every shorter stored history. -/
theorem plonkStoredColumnCostBudget_mono_columns (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare actions publicRowRead witnessRead
      thetaRead betaRead gammaRead : ℕ) (stored : StoredPlonkKey)
    {small large : ℕ} (h : small ≤ large) :
    plonkStoredColumnCostBudget costs node equal read omegaAccess canonicalRead compare actions small
      publicRowRead witnessRead thetaRead betaRead gammaRead stored ≤
      plonkStoredColumnCostBudget costs node equal read omegaAccess canonicalRead compare actions large
        publicRowRead witnessRead thetaRead betaRead gammaRead stored := by
  dsimp only [plonkStoredColumnCostBudget, plonkColumnPrepareCostBudget, plonkColumnRowCostBudget,
    storedLookupSortCostBudget, lookupSortedPrefixesCostBudget, plonkLookupCompressionCostBudget,
    plonkRowQueryCostBudget, plonkPermutationProductCostBudget, plonkPermutationFactorCostBudget,
    permutationRowNumeratorCostBudget, permutationRowDenominatorCostBudget, plonkLookupProductCostBudget,
    privateColumnRowValueCostBudget, privateColumnPolynomialEvalCostBudget]
  gcongr

end Zcash.Snark.ZeroKnowledge
