import Zcash.Snark.ZeroKnowledge.PlonkLookupProductCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- A complete bound for one real lookup-product row, including all reader preparation. -/
def plonkLookupProductCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess actions columns rowRead thetaRead betaRead gammaRead : ℕ)
    (inputExprs tableExprs : List (Expr Fp) × ℕ) : ℕ :=
  inputExprs.2 + tableExprs.2 + 2042 *
    (plonkLookupCompressionCostBudget costs node equal read omegaAccess actions columns
      rowRead thetaRead 2042 inputExprs.1 +
     plonkLookupCompressionCostBudget costs node equal read omegaAccess actions columns
      rowRead thetaRead 2042 tableExprs.1 +
     2 * privateColumnRowValueCostBudget costs equal read omegaAccess actions columns rowRead 2042 +
     2 * betaRead + 2 * gammaRead + 4 * costs.add + 4 * costs.multiply + costs.inverse + 11) + 4

/-- The real lookup-product bound discharges every row provider using the preceding costed algorithms. -/
theorem plonkLookupBaseRowsCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta beta gamma : Fp × ℕ)
    (action : Fin actions) (lookup : Fin 3) (inputExprs tableExprs : List (Expr Fp) × ℕ)
    (row : Fin 2048) (rowRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ r, (column r).2 ≤ rowRead) :
    (plonkLookupBaseRowsCosted costs node equal read omegaAccess instances fixed rows theta beta gamma
      action lookup inputExprs tableExprs row).2 ≤
      plonkLookupProductCostBudget costs node equal read omegaAccess actions rows.length
        rowRead theta.2 beta.2 gamma.2 inputExprs tableExprs := by
  by_cases hrow : row.val ≤ 2042
  · have h := lookupProductRowsCosted_cost_le costs
      (plonkLookupCompressedRowsCosted costs node equal read omegaAccess
        instances fixed rows theta action inputExprs.1)
      (plonkLookupCompressedRowsCosted costs node equal read omegaAccess
        instances fixed rows theta action tableExprs.1)
      (privateColumnRowValueCosted costs equal read omegaAccess rows (.lookupInput action lookup))
      (privateColumnRowValueCosted costs equal read omegaAccess rows (.lookupTable action lookup))
      beta gamma row.val _ _ _ _
      (fun i hi => plonkLookupCompressedRowsCosted_cost_le costs node equal read omegaAccess
        instances fixed rows theta action inputExprs.1 i 2042 rowRead (by omega) hinstances hfixed hrows)
      (fun i hi => plonkLookupCompressedRowsCosted_cost_le costs node equal read omegaAccess
        instances fixed rows theta action tableExprs.1 i 2042 rowRead (by omega) hinstances hfixed hrows)
      (fun i hi => privateColumnRowValueCosted_cost_le costs equal read omegaAccess
        rows (.lookupInput action lookup) i 2042 rowRead (by omega) hrows)
      (fun i hi => privateColumnRowValueCosted_cost_le costs equal read omegaAccess
        rows (.lookupTable action lookup) i 2042 rowRead (by omega) hrows)
    simp only [plonkLookupBaseRowsCosted, if_pos hrow]
    refine Nat.add_le_add_right (Nat.add_le_add_left h (inputExprs.2 + tableExprs.2)) 2 |>.trans ?_
    dsimp only [plonkLookupProductCostBudget]
    nlinarith
  · simp only [plonkLookupBaseRowsCosted, if_neg hrow, plonkLookupProductCostBudget]
    omega

end Zcash.Snark.ZeroKnowledge
