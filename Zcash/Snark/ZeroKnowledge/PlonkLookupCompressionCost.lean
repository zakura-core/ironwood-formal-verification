import Zcash.Snark.ZeroKnowledge.PlonkRowQueriesCost
import Zcash.Snark.ZeroKnowledge.ExpressionCompressionCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Compress an original lookup tuple from stored rows, retaining all query computation costs. -/
def plonkLookupCompressedRowsCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta : Fp × ℕ)
    (action : Fin actions) (exprs : List (Expr Fp)) (row : ℕ) : Fp × ℕ :=
  let power := fieldPowerCosted costs.multiply (omegaOf 11) row
  let point := (power.1, omegaAccess + power.2 + 1)
  let views := observeColumnRowsCosted costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)) rows
  let value := compressExprsCosted node costs.add costs.negate costs.multiply
    (plonkFixedQueryCosted costs omegaAccess fixed point)
    (plonkAdviceQueryCosted equal read views.1 action)
    (publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) point) theta exprs
  (value.1, point.2 + views.2 + value.2 + 2)

/-- Every input row, including exceptional field values, gives the original compressed value. -/
theorem plonkLookupCompressedRowsCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta : Fp × ℕ)
    (action : Fin actions) (exprs : List (Expr Fp)) (row : ℕ) :
    (plonkLookupCompressedRowsCosted costs node equal read omegaAccess
      instances fixed rows theta action exprs row).1 =
      plonkLookupCompressedRows
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) sigma)
        (rows.map (fun column r => (column r).1)) theta.1 action exprs row := by
  let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
    (fun c r => (fixed c r).1) sigma
  simp only [plonkLookupCompressedRowsCosted, compressExprsCosted_result]
  rw [show (fun index => (plonkFixedQueryCosted costs omegaAccess fixed
      ((fieldPowerCosted costs.multiply (omegaOf 11) row).1,
        omegaAccess + (fieldPowerCosted costs.multiply (omegaOf 11) row).2 + 1) index).1) =
      (fun index => (finFn (plonkPolynomialClaimProof (k := 0) (G := Fp) pub
        (rows.map (fun column r => (column r).1))).fixedEvals index).eval (omegaOf 11 ^ row)) by
    funext index
    rw [plonkRowFixedQueryCosted_result costs omegaAccess (fun a r => (instances a r).1)
      fixed sigma (rows.map (fun column r => (column r).1))]
    simp only [fieldPowerCosted_result, pub]]
  simp only [plonkObservedAdviceQueryCosted_result costs equal read omegaAccess pub,
    plonkRowInstanceQueryCosted_result costs omegaAccess instances (fun c r => (fixed c r).1)
      sigma (rows.map (fun column r => (column r).1)), fieldPowerCosted_result]
  rfl

end Zcash.Snark.ZeroKnowledge
