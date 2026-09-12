import Zcash.Snark.ZeroKnowledge.RowObservationCost
import Zcash.Snark.ZeroKnowledge.OpeningPointSetsCost
import Zcash.Snark.ZeroKnowledge.PlonkRowConstruction

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic
open CompPoly

/-- Polynomial evaluation preserves the query reader's finite-domain zero default. -/
theorem polynomialQuery_eval_finFn {count : ℕ} (values : Fin count → CPoly)
    (point : Fp) (index : ℕ) :
    (finFn values index).eval point = finFn (fun query => (values query).eval point) index := by
  by_cases hi : index < count <;> simp [finFn, hi]

/-- Counted observations and advice routing select exactly the original rotated polynomial query. -/
theorem plonkObservedAdviceQueryCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess : ℕ) {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : List (Fin 2048 → Fp × ℕ)) (point : Fp × ℕ) (action : Fin actions) (index : ℕ) :
    (plonkAdviceQueryCosted equal read
      (observeColumnRowsCosted costs omegaAccess
        (observationPointCosted costs (omegaOf 11, omegaAccess) point (0, 1)) rows).1 action index).1 =
      (finFn ((plonkPolynomialClaimProof (k := 0) (G := Fp) pub
        (rows.map (fun column row => (column row).1))).adviceEvals action) index).eval point.1 := by
  rw [plonkAdviceQueryCosted_result (k := 0) (G := Fp) equal read _ action index
    (fun a => (pub.instances a).eval point.1) (fun c => (pub.fixed c).eval point.1)
    (fun c => (pub.sigma c).eval point.1), observeColumnRowsCosted_result]
  simp only [observationPointCosted_result, polynomialQuery_eval_finFn,
    plonkPolynomialClaimProof, plonkClaimProof, plonkProofString,
    plonkRotatedColumn_eval _ _ _ point.1 0]

/-- Counted fixed queries include their original order and the complete row-polynomial evaluation. -/
theorem plonkRowFixedQueryCosted_result (costs : FieldOperationCosts) (omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp)
    (rows : ColumnHistory 2048) (point : Fp × ℕ) (index : ℕ) :
    (plonkFixedQueryCosted costs omegaAccess fixed point index).1 =
      (finFn (plonkPolynomialClaimProof (k := 0) (G := Fp)
        (plonkPublicPolynomialsFromRows instances (fun c r => (fixed c r).1) sigma)
        rows).fixedEvals index).eval point.1 := by
  rw [plonkFixedQueryCosted_result, polynomialQuery_eval_finFn]
  simp only [plonkPolynomialClaimProof, plonkClaimProof, plonkProofString,
    plonkPublicPolynomialsFromRows]
  rfl

/-- Counted instance queries retain the original one-column domain and its zero default. -/
theorem plonkRowInstanceQueryCosted_result (costs : FieldOperationCosts) (omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (rows : ColumnHistory 2048) (point : Fp × ℕ) (action : Fin actions) (index : ℕ) :
    (publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) point index).1 =
      (finFn ((plonkPolynomialClaimProof (k := 0) (G := Fp)
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1) fixed sigma)
        rows).instanceEvals action) index).eval point.1 := by
  rw [publicRowQueryCosted_result, polynomialQuery_eval_finFn]
  simp only [plonkPolynomialClaimProof, plonkClaimProof, plonkProofString,
    plonkPublicPolynomialsFromRows]
  rfl

end Zcash.Snark.ZeroKnowledge
