import Zcash.Snark.ZeroKnowledge.PlonkClaimInputsCost

/-!
# Counted lookup-input preparation

Every lookup record is materialized from the original disclosed columns and
paired with its actual input and table expression lists. The complete expression-
reader costs remain in preparation; constraint evaluation separately charges
the stored expression trees and materialized scalar fields.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Materialize one complete lookup argument's disclosed record and expression lists. -/
def plonkLookupInputCosted (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) (index : Fin 3) :
    (LookupEval (Fp × ℕ) × List (Expr Fp) × List (Expr Fp)) × ℕ :=
  let evaluation := plonkLookupEvalCosted equal read views action index
  let input := inputs index
  let table := tables index
  ((evaluation.1, input.1, table.1), evaluation.2 + input.2 + table.2 + 3)

/-- Erasure retains the original disclosed lookup record and both actual expression lists. -/
theorem plonkLookupInputCosted_result (equal read : ℕ) {actions k : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) (index : Fin 3)
    {G : Type*} [Zero G] (instances : Fin actions → Fp) (fixed : Fin 29 → Fp) (sigma : Fin 15 → Fp) :
    let result := (plonkLookupInputCosted equal read views action inputs tables index).1
    (result.1.map Prod.fst, result.2.1, result.2.2) =
      ((plonkClaimProof (k := k) (G := G) instances fixed sigma
        (fun id point => privateColumnView (views.map (fun column i => (column i).1)) id point.castSucc)).lookupEvals
        action index, (inputs index).1, (tables index).1) := by
  simp only [plonkLookupInputCosted,
    plonkLookupEvalCosted_result (k := k) (G := G) equal read views action index instances fixed sigma]

/-- The stored lookup fields are materialized before any constraint expression reads them. -/
theorem plonkLookupInputCosted_readBound (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) (index : Fin 3) :
    lookupEvalReadBound (plonkLookupInputCosted equal read views action inputs tables index).1.1 1 :=
  plonkLookupEvalCosted_readBound equal read views action index

/-- Lookup preparation includes every column route and both complete expression-list reads. -/
theorem plonkLookupInputCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) (index : Fin 3)
    (access inputAccess tableAccess : ℕ)
    (hviews : ∀ column ∈ views, ∀ point, (column point).2 ≤ access)
    (hinput : ∀ index, (inputs index).2 ≤ inputAccess) (htable : ∀ index, (tables index).2 ≤ tableAccess) :
    let budget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
      2 * views.length + read + access + 15
    (plonkLookupInputCosted equal read views action inputs tables index).2 ≤
      5 * budget + inputAccess + tableAccess + 14 := by
  have hv := plonkLookupEvalCosted_cost_le equal read views action index access hviews
  have hi := hinput index
  have ht := htable index
  dsimp only [plonkLookupInputCosted]
  omega

/-- Materialize all three complete lookup arguments in the original order. -/
def plonkLookupInputsCosted (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) :
    List (LookupEval (Fp × ℕ) × List (Expr Fp) × List (Expr Fp)) × ℕ :=
  ofFnCosted (plonkLookupInputCosted equal read views action inputs tables)

/-- The complete materialized list has exactly the verifier's lookup-evaluation and expression order. -/
theorem plonkLookupInputsCosted_result (equal read : ℕ) {actions k : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    {G : Type*} [Zero G] (instances : Fin actions → Fp) (fixed : Fin 29 → Fp) (sigma : Fin 15 → Fp) :
    (plonkLookupInputsCosted equal read views action inputs tables).1.map
        (fun lookup => (lookup.1.map Prod.fst, lookup.2.1, lookup.2.2)) =
      List.ofFn (fun index =>
        ((plonkClaimProof (k := k) (G := G) instances fixed sigma
          (fun id point => privateColumnView (views.map (fun column i => (column i).1)) id point.castSucc)).lookupEvals
          action index, (inputs index).1, (tables index).1)) := by
  simp only [plonkLookupInputsCosted, ofFnCosted_result, List.map_ofFn, Function.comp_def,
    plonkLookupInputCosted_result (k := k) (G := G) equal read views action inputs tables _ instances fixed sigma]
  rfl

/-- All three lookup arguments are fully materialized. -/
theorem plonkLookupInputsCosted_length (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) :
    (plonkLookupInputsCosted equal read views action inputs tables).1.length = 3 := ofFnCosted_length _

/-- Complete lookup-list preparation retains all scalar and expression-reader costs. -/
theorem plonkLookupInputsCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (inputs tables : Fin 3 → List (Expr Fp) × ℕ) (access inputAccess tableAccess : ℕ)
    (hviews : ∀ column ∈ views, ∀ point, (column point).2 ≤ access)
    (hinput : ∀ index, (inputs index).2 ≤ inputAccess) (htable : ∀ index, (tables index).2 ≤ tableAccess) :
    let budget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
      2 * views.length + read + access + 15
    (plonkLookupInputsCosted equal read views action inputs tables).2 ≤
      3 * (5 * budget + inputAccess + tableAccess + 15) + 10 := by
  exact ofFnCosted_cost_le _ _ (fun index => plonkLookupInputCosted_cost_le
    equal read views action inputs tables index access inputAccess tableAccess hviews hinput htable)

end Zcash.Snark.ZeroKnowledge
