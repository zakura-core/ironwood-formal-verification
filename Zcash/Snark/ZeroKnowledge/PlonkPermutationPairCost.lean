import Zcash.Snark.ZeroKnowledge.PlonkRowQueriesCostBound
import Zcash.Snark.ZeroKnowledge.PermutationQueryPreparationCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic
open CompPoly

/-- Evaluating a selected polynomial preserves all three original column-reference routes. -/
theorem columnRef_resolve_polynomial_eval (reference : ColumnRef)
    (instances advice fixed : ℕ → CPoly) (point : Fp) :
    (reference.resolve instances advice fixed).eval point =
      reference.resolve (fun i => (instances i).eval point)
        (fun i => (advice i).eval point) (fun i => (fixed i).eval point) := by
  cases reference <;> rfl

/-- Materialize one real permutation pair with complete public and private polynomial queries. -/
def plonkPermutationPairAtPointCosted (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (point : Fp × ℕ) (action : Fin actions)
    (entry : ColumnRef × ℕ) : (Fp × Fp) × ℕ :=
  let views := observeColumnRowsCosted costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)) rows
  let pair := permutationColumnPairCosted
    (publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) point)
    (plonkAdviceQueryCosted equal read views.1 action)
    (plonkFixedQueryCosted costs omegaAccess fixed point)
    (publicRowQueryCosted costs omegaAccess sigma point) entry
  (pair.1.1, views.2 + pair.2 + 1)

/-- The real pair contains the original resolved polynomial and sigma evaluation. -/
theorem plonkPermutationPairAtPointCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (point : Fp × ℕ) (action : Fin actions)
    (entry : ColumnRef × ℕ) :
    (plonkPermutationPairAtPointCosted costs equal read omegaAccess
      instances fixed sigma rows point action entry).1 =
      let ps := plonkPolynomialClaimProof (k := 0) (G := Fp)
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (rows.map (fun column r => (column r).1))
      ((entry.1.resolve (finFn (ps.instanceEvals action)) (finFn (ps.adviceEvals action))
          (finFn ps.fixedEvals)).eval point.1,
        (finFn ps.permutationCommonEvals entry.2).eval point.1) := by
  let pub := plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
    (fun c r => (fixed c r).1) (fun c r => (sigma c r).1)
  simp only [plonkPermutationPairAtPointCosted, permutationColumnPairCosted_result,
    plonkObservedAdviceQueryCosted_result costs equal read omegaAccess pub,
    plonkRowFixedQueryCosted_result costs omegaAccess (fun a r => (instances a r).1)
      fixed (fun c r => (sigma c r).1) (rows.map (fun column r => (column r).1)),
    plonkRowInstanceQueryCosted_result costs omegaAccess instances (fun c r => (fixed c r).1)
      (fun c r => (sigma c r).1) (rows.map (fun column r => (column r).1)),
    columnRef_resolve_polynomial_eval]
  congr 1
  rw [publicRowQueryCosted_result, polynomialQuery_eval_finFn]
  simp only [plonkPolynomialClaimProof, plonkClaimProof, plonkProofString, plonkPublicPolynomialsFromRows]
  rfl

end Zcash.Snark.ZeroKnowledge
