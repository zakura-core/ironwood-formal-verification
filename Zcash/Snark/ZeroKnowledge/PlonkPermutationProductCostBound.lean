import Zcash.Snark.ZeroKnowledge.PlonkPermutationProductCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Complete three-chunk scan budget, including original factor preparation and inherited states. -/
def plonkPermutationProductCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess actions columns rowRead betaRead gammaRead deltaRead : ℕ)
    (chunkLen : ℕ × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ) : ℕ :=
  let pairsCost := plonkPermutationFactorCostBudget costs equal read omegaAccess actions columns rowRead 2042
    layout.2 layout.1.length (layout.1.map List.length).sum
  let numerator := permutationRowNumeratorCostBudget costs read pairsCost (layout.1.map List.length).sum
    betaRead gammaRead omegaAccess deltaRead chunkLen.1 2 2042
  let denominator := permutationRowDenominatorCostBudget costs read pairsCost (layout.1.map List.length).sum
    betaRead gammaRead
  chunkLen.2 + 6126 * (numerator + denominator + 2 * costs.multiply + costs.inverse + 5) + 8

/-- The real permutation constructor's complete bound is discharged from its counted row queries. -/
theorem plonkPermutationBaseRowsCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (beta gamma delta : Fp × ℕ)
    (chunkLen : ℕ × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ)
    (action : Fin actions) (set : Fin 3) (row : Fin 2048) (rowRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead) (hsigma : ∀ c r, (sigma c r).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ r, (column r).2 ≤ rowRead) :
    (plonkPermutationBaseRowsCosted costs equal read omegaAccess instances fixed sigma rows beta gamma delta
      chunkLen layout action set row).2 ≤
      plonkPermutationProductCostBudget costs equal read omegaAccess actions rows.length rowRead
        beta.2 gamma.2 delta.2 chunkLen layout := by
  by_cases hrow : row.val ≤ 2042
  · let pairs := plonkPermutationFactorRowsCosted costs equal read omegaAccess instances fixed sigma rows action layout
    let pairsCost := plonkPermutationFactorCostBudget costs equal read omegaAccess actions rows.length rowRead 2042
      layout.2 layout.1.length (layout.1.map List.length).sum
    let numerator := permutationRowNumeratorCosted costs read pairs beta gamma (omegaOf 11, omegaAccess) delta chunkLen.1
    let denominator := permutationRowDenominatorCosted costs read pairs beta gamma
    let numBound := permutationRowNumeratorCostBudget costs read pairsCost (layout.1.map List.length).sum
      beta.2 gamma.2 omegaAccess delta.2 chunkLen.1 2 2042
    let denBound := permutationRowDenominatorCostBudget costs read pairsCost (layout.1.map List.length).sum beta.2 gamma.2
    have hp (c i : ℕ) (hi : i < 2042) : (pairs c i).2 ≤ pairsCost :=
      plonkPermutationFactorRowsCosted_cost_le costs equal read omegaAccess instances fixed sigma rows action layout
        c i 2042 rowRead (Nat.le_of_lt hi) hinstances hfixed hsigma hrows
    have hl (c i : ℕ) : (pairs c i).1.length ≤ (layout.1.map List.length).sum := by
      rw [plonkPermutationFactorRowsCosted_length]
      exact listGetD_length_le_sum layout.1 c
    have hn (c : ℕ) (hc : c ≤ set.val) (i : ℕ) (hi : i < 2042) : (numerator c i).2 ≤ numBound := by
      have hs := set.isLt
      exact (permutationRowNumeratorCosted_cost_le costs read pairs beta gamma
        (omegaOf 11, omegaAccess) delta chunkLen.1 c i).trans
        (permutationRowNumeratorCostBudget_mono costs read beta.2 gamma.2 omegaAccess delta.2 chunkLen.1
          (hp c i hi) (hl c i) (by omega) (Nat.le_of_lt hi))
    have hd (c : ℕ) (_ : c ≤ set.val) (i : ℕ) (hi : i < 2042) : (denominator c i).2 ≤ denBound :=
      (permutationRowDenominatorCosted_cost_le costs read pairs beta gamma c i).trans
        (permutationRowDenominatorCostBudget_mono costs read beta.2 gamma.2 (hp c i hi) (hl c i))
    have h := chainedProductRowsCosted_cost_le costs numerator denominator 2042 set.val row.val
      numBound denBound hrow hn hd
    simp only [plonkPermutationBaseRowsCosted, if_pos hrow]
    change chunkLen.2 + (chainedProductRowsCosted costs numerator denominator 2042 set.val row.val).2 + 2 ≤ _
    change _ ≤ chunkLen.2 + 6126 * (numBound + denBound + 2 * costs.multiply + costs.inverse + 5) + 8
    have hs := set.isLt
    nlinarith
  · simp only [plonkPermutationBaseRowsCosted, if_neg hrow, plonkPermutationProductCostBudget]
    omega

end Zcash.Snark.ZeroKnowledge
