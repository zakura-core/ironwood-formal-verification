import Zcash.Snark.ZeroKnowledge.PrivateColumnRoutingCost
import Zcash.Snark.ZeroKnowledge.PermutationBoundaryCost
import Zcash.Snark.ZeroKnowledge.LookupExpressionsCost
import Zcash.Snark.ZeroKnowledge.QueryOrderCost
import Zcash.Snark.ZeroKnowledge.PlonkProofString

/-!
# Counted construction of disclosed PLONK constraint inputs

Permutation and lookup records are fully materialized from the original column
observations. Their preparation pays for every column lookup; later reads of
the stored scalar fields cost one structural unit. Advice queries retain the
actual query-table selection and complete selected-column reader cost.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Materialize one original permutation record, including the optional last-row observation. -/
def plonkPermutationSetCosted (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (set : Fin 3) : PermSetEval (Fp × ℕ) × ℕ :=
  let current := privateColumnViewCosted equal read views (.permutationProduct action set) 0
  let next := privateColumnViewCosted equal read views (.permutationProduct action set) 1
  let last : Option (Fp × ℕ) × ℕ := if set.val < 2 then
    let value := privateColumnViewCosted equal read views (.permutationProduct action set) 3
    (some (value.1, 1), value.2 + 1)
    else (none, 1)
  ({ eval := (current.1, 1), nextEval := (next.1, 1), lastEval := last.1 },
    current.2 + next.2 + last.2 + 7)

/-- Erasure is the actual claim proof's permutation record, including its last-row condition. -/
theorem plonkPermutationSetCosted_result (equal read : ℕ) {actions k : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (set : Fin 3)
    {G : Type*} [Zero G] (instances : Fin actions → Fp) (fixed : Fin 29 → Fp) (sigma : Fin 15 → Fp) :
    ((plonkPermutationSetCosted equal read views action set).1.map Prod.fst) =
      (plonkClaimProof (k := k) (G := G) instances fixed sigma
        (fun id point => privateColumnView (views.map (fun column index => (column index).1)) id point.castSucc)).permutationSetEvals
        action set := by
  by_cases h : set.val < 2 <;>
    simp [plonkPermutationSetCosted, h, PermSetEval.map, privateColumnViewCosted_result,
      plonkClaimProof, plonkProofString]
  all_goals omega

/-- All fields in the produced permutation record are already materialized. -/
theorem plonkPermutationSetCosted_readBound (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (set : Fin 3) :
    permSetReadBound (plonkPermutationSetCosted equal read views action set).1 1 := by
  by_cases h : set.val < 2 <;> simp [plonkPermutationSetCosted, h, permSetReadBound]

/-- The preparation budget pays for all routed observations and the optional-field branch. -/
theorem plonkPermutationSetCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (set : Fin 3)
    (access : ℕ) (hviews : ∀ column ∈ views, ∀ index, (column index).2 ≤ access) :
    let budget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
      2 * views.length + read + access + 15
    (plonkPermutationSetCosted equal read views action set).2 ≤ 3 * budget + 8 := by
  have hcurrent := privateColumnViewCosted_cost_le equal read views (.permutationProduct action set) 0 access hviews
  have hnext := privateColumnViewCosted_cost_le equal read views (.permutationProduct action set) 1 access hviews
  have hlast := privateColumnViewCosted_cost_le equal read views (.permutationProduct action set) 3 access hviews
  dsimp only
  by_cases h : set.val < 2 <;> simp only [plonkPermutationSetCosted, h, if_true, if_false] <;> omega

/-- Materialize every permutation set in the actual three-set order. -/
def plonkPermutationSetsCosted (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) : List (PermSetEval (Fp × ℕ)) × ℕ :=
  ofFnCosted (plonkPermutationSetCosted equal read views action)

/-- The materialized set list erases to the verifier's exact original preparation. -/
theorem plonkPermutationSetsCosted_result (equal read : ℕ) {actions k : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    {G : Type*} [Zero G] (instances : Fin actions → Fp) (fixed : Fin 29 → Fp) (sigma : Fin 15 → Fp) :
    (plonkPermutationSetsCosted equal read views action).1.map (PermSetEval.map Prod.fst) =
      subProofPermSets (plonkClaimProof (k := k) (G := G) instances fixed sigma
        (fun id point => privateColumnView (views.map (fun column index => (column index).1)) id point.castSucc)) action := by
  simp only [plonkPermutationSetsCosted, ofFnCosted_result, List.map_ofFn, Function.comp_def,
    plonkPermutationSetCosted_result (k := k) (G := G) equal read views action _ instances fixed sigma,
    subProofPermSets]
  rfl

/-- Every original permutation set is materialized. -/
theorem plonkPermutationSetsCosted_length (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) :
    (plonkPermutationSetsCosted equal read views action).1.length = 3 := ofFnCosted_length _

/-- All permutation-set preparation costs remain in the complete three-record budget. -/
theorem plonkPermutationSetsCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions)
    (access : ℕ) (hviews : ∀ column ∈ views, ∀ index, (column index).2 ≤ access) :
    let budget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
      2 * views.length + read + access + 15
    (plonkPermutationSetsCosted equal read views action).2 ≤ 3 * (3 * budget + 9) + 10 := by
  exact ofFnCosted_cost_le _ _ (fun set => plonkPermutationSetCosted_cost_le equal read views action set access hviews)

/-- Materialize all five original disclosed fields for one lookup argument. -/
def plonkLookupEvalCosted (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (lookup : Fin 3) : LookupEval (Fp × ℕ) × ℕ :=
  let product := privateColumnViewCosted equal read views (.lookupProduct action lookup) 0
  let next := privateColumnViewCosted equal read views (.lookupProduct action lookup) 1
  let input := privateColumnViewCosted equal read views (.lookupInput action lookup) 0
  let inverseInput := privateColumnViewCosted equal read views (.lookupInput action lookup) 2
  let table := privateColumnViewCosted equal read views (.lookupTable action lookup) 0
  ({ productEval := (product.1, 1), productNextEval := (next.1, 1),
      permutedInputEval := (input.1, 1), permutedInputInvEval := (inverseInput.1, 1), permutedTableEval := (table.1, 1) },
    product.2 + next.2 + input.2 + inverseInput.2 + table.2 + 11)

/-- Erasure gives the actual claim proof's five-field lookup record. -/
theorem plonkLookupEvalCosted_result (equal read : ℕ) {actions k : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (lookup : Fin 3)
    {G : Type*} [Zero G] (instances : Fin actions → Fp) (fixed : Fin 29 → Fp) (sigma : Fin 15 → Fp) :
    ((plonkLookupEvalCosted equal read views action lookup).1.map Prod.fst) =
      (plonkClaimProof (k := k) (G := G) instances fixed sigma
        (fun id point => privateColumnView (views.map (fun column index => (column index).1)) id point.castSucc)).lookupEvals
        action lookup := by
  simp only [plonkLookupEvalCosted, LookupEval.map, privateColumnViewCosted_result, plonkClaimProof, plonkProofString]
  rfl

/-- Every disclosed lookup scalar is already materialized. -/
theorem plonkLookupEvalCosted_readBound (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (lookup : Fin 3) :
    lookupEvalReadBound (plonkLookupEvalCosted equal read views action lookup).1 1 := by
  simp only [plonkLookupEvalCosted, lookupEvalReadBound]
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- All five original column routes are paid during lookup-record preparation. -/
theorem plonkLookupEvalCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (lookup : Fin 3)
    (access : ℕ) (hviews : ∀ column ∈ views, ∀ index, (column index).2 ≤ access) :
    let budget := 4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
      2 * views.length + read + access + 15
    (plonkLookupEvalCosted equal read views action lookup).2 ≤ 5 * budget + 11 := by
  have hp := privateColumnViewCosted_cost_le equal read views (.lookupProduct action lookup) 0 access hviews
  have hn := privateColumnViewCosted_cost_le equal read views (.lookupProduct action lookup) 1 access hviews
  have hi := privateColumnViewCosted_cost_le equal read views (.lookupInput action lookup) 0 access hviews
  have hv := privateColumnViewCosted_cost_le equal read views (.lookupInput action lookup) 2 access hviews
  have ht := privateColumnViewCosted_cost_le equal read views (.lookupTable action lookup) 0 access hviews
  dsimp only [plonkLookupEvalCosted]
  omega

/-- Resolve an original advice query through the counted query table and private-column route. -/
def plonkAdviceClaimCosted (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (index : Fin 25) : Fp × ℕ :=
  let query := adviceQueryOrderCosted index
  let value := privateColumnViewCosted equal read views (.advice action query.1.1) (query.1.2.castLE (by decide))
  (value.1, query.2 + value.2 + 1)

/-- Advice-query erasure is the selected field of the existing claim proof. -/
theorem plonkAdviceClaimCosted_result (equal read : ℕ) {actions k : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (index : Fin 25)
    {G : Type*} [Zero G] (instances : Fin actions → Fp) (fixed : Fin 29 → Fp) (sigma : Fin 15 → Fp) :
    (plonkAdviceClaimCosted equal read views action index).1 =
      (plonkClaimProof (k := k) (G := G) instances fixed sigma
        (fun id point => privateColumnView (views.map (fun column i => (column i).1)) id point.castSucc)).adviceEvals
        action index := by
  simp only [plonkAdviceClaimCosted, privateColumnViewCosted_result, adviceQueryOrderCosted_result,
    plonkClaimProof, plonkProofString]
  rfl

/-- Advice-query costs include the complete query table and the selected column reader. -/
theorem plonkAdviceClaimCosted_cost_le (equal read : ℕ) {actions : ℕ}
    (views : List (Fin 5 → Fp × ℕ)) (action : Fin actions) (index : Fin 25)
    (access : ℕ) (hviews : ∀ column ∈ views, ∀ point, (column point).2 ≤ access) :
    (plonkAdviceClaimCosted equal read views action index).2 ≤
      4 * actions * actions + 260 * actions + (22 * actions) * (equal + 2) +
        2 * views.length + read + access + 169 := by
  have hquery := adviceQueryOrderCosted_cost_le index
  have hvalue := privateColumnViewCosted_cost_le equal read views
    (.advice action (adviceQueryOrderCosted index).1.1)
    ((adviceQueryOrderCosted index).1.2.castLE (by decide)) access hviews
  simp only [plonkAdviceClaimCosted]
  omega

end Zcash.Snark.ZeroKnowledge
