import Zcash.Snark.ZeroKnowledge.PlonkPermutationFactorsCostBound
import Zcash.Snark.ZeroKnowledge.PermutationRowProductCostMono
import Zcash.Snark.ZeroKnowledge.RunningProductCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Compute a real permutation-product row with every earlier chunk and complete factor queries. -/
def plonkPermutationBaseRowsCosted (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (beta gamma delta : Fp × ℕ)
    (chunkLen : ℕ × ℕ) (layout : List (List (ColumnRef × ℕ)) × ℕ)
    (action : Fin actions) (set : Fin 3) (row : Fin 2048) : Fp × ℕ :=
  if row.val ≤ 2042 then
    let pairs := plonkPermutationFactorRowsCosted costs equal read omegaAccess instances fixed sigma rows action layout
    let value := chainedProductRowsCosted costs
      (permutationRowNumeratorCosted costs read pairs beta gamma (omegaOf 11, omegaAccess) delta chunkLen.1)
      (permutationRowDenominatorCosted costs read pairs beta gamma) 2042 set.val row.val
    (value.1, chunkLen.2 + value.2 + 2)
  else (0, 1)

/-- Every row equals the original real constructor, including inherited chunks and zero factors. -/
theorem plonkPermutationBaseRowsCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (beta gamma : Fp × ℕ)
    (deltaRead chunkLenRead layoutRead : ℕ) (action : Fin actions) (set : Fin 3) (row : Fin 2048) :
    (plonkPermutationBaseRowsCosted costs equal read omegaAccess instances fixed sigma rows beta gamma
      (vk.delta, deltaRead) (vk.chunkLen, chunkLenRead) (vk.permutationChunks, layoutRead) action set row).1 =
      plonkPermutationBaseRows vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (rows.map (fun column r => (column r).1)) beta.1 gamma.1 action set row := by
  by_cases hrow : row.val ≤ 2042 <;>
    simp only [plonkPermutationBaseRowsCosted, plonkPermutationBaseRows, hrow, if_true, if_false,
      chainedProductRowsCosted_result, permutationRowNumeratorCosted_result,
      permutationRowDenominatorCosted_result, plonkPermutationFactorRowsCosted_result, permutationScanRows]

end Zcash.Snark.ZeroKnowledge
