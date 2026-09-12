import Zcash.Snark.ZeroKnowledge.PlonkClaimInputsCost
import Zcash.Snark.ZeroKnowledge.PublicOpeningClaimsCost
import Zcash.Snark.ZeroKnowledge.QueryRoutingCost

/-!
# Counted query readers for the original PLONK claims

Public row queries include full polynomial coefficient preparation and evaluation.
Fixed and advice queries follow their original finite tables. Every reader uses
the verifier's zero default outside its finite domain and retains the complete
cost of its selected input computation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp omegaOf)

/-- Read a finite public polynomial family, including row preparation and the original zero default. -/
def publicRowQueryCosted (costs : FieldOperationCosts) (omegaAccess : ℕ) {count : ℕ}
    (rows : Fin count → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (index : ℕ) : Fp × ℕ :=
  finFnCosted (fun column => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) (rows column) point) index

/-- Erasure is the finite-to-total query reader for the canonical public row polynomials. -/
theorem publicRowQueryCosted_result (costs : FieldOperationCosts) (omegaAccess : ℕ) {count : ℕ}
    (rows : Fin count → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (index : ℕ) :
    (publicRowQueryCosted costs omegaAccess rows point index).1 =
      finFn (fun column => (rowPolynomial (omegaOf 11) (fun row => (rows column row).1)).eval point.1) index := by
  simp only [publicRowQueryCosted, finFnCosted_result,
    rowPolynomialEvalCosted_result costs 11 (by decide) omegaAccess]
  rfl

/-- A public query pays for all inverse-DFT and evaluation work before its result is read. -/
theorem publicRowQueryCosted_cost_le (costs : FieldOperationCosts) (omegaAccess : ℕ) {count : ℕ}
    (rows : Fin count → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (index : ℕ)
    (rowRead : ℕ) (hrows : ∀ column row, (rows column row).2 ≤ rowRead) :
    (publicRowQueryCosted costs omegaAccess rows point index).2 ≤
      publicRowEvaluationCostBudget costs rowRead omegaAccess point.2 + 1 := by
  apply finFnCosted_cost_le
  intro column
  have h := rowPolynomialEvalCosted_cost_le costs (omegaOf 11, omegaAccess) (rows column) point rowRead (hrows column)
  dsimp only at h
  exact h

/-- Resolve an original fixed query with full query-table and row-polynomial preparation costs. -/
def plonkFixedQueryCosted (costs : FieldOperationCosts) (omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (index : ℕ) : Fp × ℕ :=
  finFnCosted (fixedRowEvaluationCosted costs omegaAccess fixed point) index

/-- Fixed-query erasure follows the original query order and out-of-range behavior. -/
theorem plonkFixedQueryCosted_result (costs : FieldOperationCosts) (omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (index : ℕ) :
    (plonkFixedQueryCosted costs omegaAccess fixed point index).1 =
      finFn (fun query =>
        (rowPolynomial (omegaOf 11) (fun row => (fixed (plonkFixedQueryOrder query) row).1)).eval point.1) index := by
  simp only [plonkFixedQueryCosted, finFnCosted_result, fixedRowEvaluationCosted_result]

/-- The fixed-query budget includes its actual table lookup and complete polynomial computation. -/
theorem plonkFixedQueryCosted_cost_le (costs : FieldOperationCosts) (omegaAccess : ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (point : Fp × ℕ) (index : ℕ)
    (rowRead : ℕ) (hfixed : ∀ column row, (fixed column row).2 ≤ rowRead) :
    (plonkFixedQueryCosted costs omegaAccess fixed point index).2 ≤
      publicRowEvaluationCostBudget costs rowRead omegaAccess point.2 + 121 := by
  have h := finFnCosted_cost_le (fixedRowEvaluationCosted costs omegaAccess fixed point)
    (publicRowEvaluationCostBudget costs rowRead omegaAccess point.2 + 120)
    (fun query => fixedRowEvaluationCosted_cost_le costs omegaAccess fixed point query rowRead hfixed) index
  change (finFnCosted (fixedRowEvaluationCosted costs omegaAccess fixed point) index).2 ≤ _
  omega

/-- Resolve an original advice query, including the outer finite-domain check. -/
def plonkAdviceQueryCosted (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (index : ℕ) : Fp × ℕ :=
  finFnCosted (plonkAdviceClaimCosted equal read views action) index

/-- The complete advice reader is exactly the claim proof's finite-to-total query function. -/
theorem plonkAdviceQueryCosted_result (equal read : ℕ) {actions k : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (index : ℕ)
    {G : Type*} [Zero G] (instances : Fin actions → Fp) (fixed : Fin 29 → Fp) (sigma : Fin 15 → Fp) :
    (plonkAdviceQueryCosted equal read views action index).1 =
      finFn ((plonkClaimProof (k := k) (G := G) instances fixed sigma
        (fun id point => privateColumnView (views.map (fun column i => (column i).1)) id point.castSucc)).adviceEvals action)
        index := by
  simp only [plonkAdviceQueryCosted, finFnCosted_result,
    plonkAdviceClaimCosted_result (k := k) (G := G) equal read views action _ instances fixed sigma]
  rfl

/-- Every advice-query branch retains its complete original query-table and column-reader costs. -/
theorem plonkAdviceQueryCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (index : ℕ)
    (access : ℕ) (hviews : ∀ column ∈ views, ∀ point, (column point).2 ≤ access) :
    (plonkAdviceQueryCosted equal read views action index).2 ≤
      4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
        2 * views.length + read + access + 170 := by
  have h := finFnCosted_cost_le (plonkAdviceClaimCosted equal read views action)
    (4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
      2 * views.length + read + access + 169)
    (fun query => plonkAdviceClaimCosted_cost_le equal read views action query access hviews) index
  change (finFnCosted (plonkAdviceClaimCosted equal read views action) index).2 ≤ _
  omega

end Zcash.Snark.ZeroKnowledge
