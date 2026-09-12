import Zcash.Snark.ZeroKnowledge.PlonkLookupCompressionCostBound
import Zcash.Snark.ZeroKnowledge.PrivateRowValueCost
import Zcash.Snark.ZeroKnowledge.RunningProductCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Compute a real lookup-product row from its original compressed and permuted column feeds. -/
def plonkLookupBaseRowsCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta beta gamma : Fp × ℕ)
    (action : Fin actions) (lookup : Fin 3) (inputExprs tableExprs : List (Expr Fp) × ℕ)
    (row : Fin 2048) : Fp × ℕ :=
  if row.val ≤ 2042 then
    let value := lookupProductRowsCosted costs
      (plonkLookupCompressedRowsCosted costs node equal read omegaAccess
        instances fixed rows theta action inputExprs.1)
      (plonkLookupCompressedRowsCosted costs node equal read omegaAccess
        instances fixed rows theta action tableExprs.1)
      (privateColumnRowValueCosted costs equal read omegaAccess rows (.lookupInput action lookup))
      (privateColumnRowValueCosted costs equal read omegaAccess rows (.lookupTable action lookup))
      beta gamma row.val
    (value.1, inputExprs.2 + tableExprs.2 + value.2 + 2)
  else (0, 1)

/-- Every retained or suffix row agrees with the original product constructor, including zero factors. -/
theorem plonkLookupBaseRowsCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta beta gamma : Fp × ℕ)
    (action : Fin actions) (lookup : Fin 3) (inputRead tableRead : ℕ) (row : Fin 2048) :
    (plonkLookupBaseRowsCosted costs node equal read omegaAccess instances fixed rows theta beta gamma
      action lookup (vk.lookupInputExprs lookup, inputRead) (vk.lookupTableExprs lookup, tableRead) row).1 =
      plonkLookupBaseRows vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1) (fun c r => (fixed c r).1) sigma)
        (rows.map (fun column r => (column r).1)) theta.1 beta.1 gamma.1 action lookup row := by
  by_cases hrow : row.val ≤ 2042 <;>
    simp only [plonkLookupBaseRowsCosted, plonkLookupBaseRows, hrow, if_true, if_false,
      lookupProductRowsCosted_result,
      plonkLookupCompressedRowsCosted_result costs node equal read omegaAccess instances fixed sigma,
      privateColumnRowValueCosted_result]

end Zcash.Snark.ZeroKnowledge
