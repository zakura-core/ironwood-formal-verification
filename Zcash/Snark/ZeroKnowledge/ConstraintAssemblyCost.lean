import Zcash.Snark.ZeroKnowledge.PermutationExpressionsCost
import Zcash.Snark.ZeroKnowledge.LookupExpressionsCost
import Zcash.Snark.ZeroKnowledge.ListCollectedCost

/-!
# Counted assembly of all constraints for one sub-proof

The algorithm evaluates the original gate trees, complete permutation list, and
all lookup constraints, then constructs the verifier's complete ordered list.
The budgets use actual materialized input sizes and complete field-reader costs.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Each member's nonnegative size is bounded by the sum of all materialized member sizes. -/
theorem listValue_le_map_sum {α : Type*} (measure : α → ℕ) (values : List α)
    (value : α) (hmem : value ∈ values) : measure value ≤ (values.map measure).sum := by
  induction values with
  | nil => simp at hmem
  | cons first rest ih =>
    rcases List.mem_cons.mp hmem with h | h
    · subst value
      simp
    · have hrest := ih h
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The complete counted permutation list has at most two boundary, one-per-set, and one-per-chunk values. -/
theorem permutationExpressionsCosted_length_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (beta gamma x delta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ) :
    (permutationExpressionsCosted costs sets chunks beta gamma x delta chunkLen l0 lLast lBlind).1.length ≤
      sets.length + chunks.length + 2 := by
  have hfirst := permutationFirstCosted_length_le costs sets l0
  have hlast := permutationLastCosted_length_le costs sets lLast
  simp only [permutationExpressionsCosted, appendListCosted_result, List.length_append,
    mapListCosted_result, mapIndexListCosted_result, zipListCosted_result,
    List.length_map, List.length_zip, List.length_range', min_self, List.length_tail]
  omega

/-- The counted lookup calculation always produces all five original constraint values. -/
theorem lookupExpressionsCosted_length {F : Type*} [CommRing F] (costs : FieldOperationCosts) (node : ℕ)
    (le : LookupEval (F × ℕ)) (inputExprs tableExprs : List (Expr F))
    (fixed advice instanceRead : ℕ → F × ℕ) (theta beta gamma l0 lLast lBlind : F × ℕ) :
    (lookupExpressionsCosted costs node le inputExprs tableExprs fixed advice instanceRead
      theta beta gamma l0 lLast lBlind).1.length = 5 := by
  rw [lookupExpressionsCosted_result]
  rfl

/-- Evaluate and materialize one sub-proof's complete gate, permutation, and lookup list. -/
def subProofConstraintsCosted {F : Type*} [CommRing F] (costs : FieldOperationCosts) (node : ℕ)
    (fixed advice instanceRead : ℕ → F × ℕ) (gates : List (Expr F))
    (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (lookups : List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ) : List F × ℕ :=
  let gateValues := mapListCosted (exprEvalCosted node costs.add costs.negate costs.multiply fixed advice instanceRead) gates
  let permutation := permutationExpressionsCosted costs sets chunks beta gamma x delta chunkLen l0 lLast lBlind
  let lookupValues := flatMapListCosted (fun lookup =>
    lookupExpressionsCosted costs node lookup.1 lookup.2.1 lookup.2.2 fixed advice instanceRead
      theta beta gamma l0 lLast lBlind) lookups
  let initial := appendListCosted gateValues.1 permutation.1
  let result := appendListCosted initial.1 lookupValues.1
  (result.1, gateValues.2 + permutation.2 + lookupValues.2 + initial.2 + result.2 + 1)

/-- Erasure preserves every original constraint and the complete verifier ordering. -/
theorem subProofConstraintsCosted_result {F : Type*} [CommRing F] (costs : FieldOperationCosts) (node : ℕ)
    (fixed advice instanceRead : ℕ → F × ℕ) (gates : List (Expr F))
    (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (lookups : List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ) :
    (subProofConstraintsCosted costs node fixed advice instanceRead gates sets chunks lookups
      beta gamma x delta theta chunkLen l0 lLast lBlind).1 =
      subProofConstraints (fun index => (fixed index).1) (fun index => (advice index).1)
        (fun index => (instanceRead index).1) gates (sets.map (PermSetEval.map Prod.fst))
        (chunks.map (fun chunk => (chunk.1.map Prod.fst, chunk.2.map Prod.fst)))
        (lookups.map (fun lookup => (lookup.1.map Prod.fst, lookup.2.1, lookup.2.2)))
        beta.1 gamma.1 x.1 delta.1 theta.1 chunkLen l0.1 lLast.1 lBlind.1 := by
  simp only [subProofConstraintsCosted, appendListCosted_result, mapListCosted_result,
    exprEvalCosted_result, permutationExpressionsCosted_result, flatMapListCosted_result,
    lookupExpressionsCosted_result, subProofConstraints, List.map_map, List.flatMap,
    Function.comp_def]

/-- Permutation budget using the actual lists and their total number of stored column pairs. -/
def subProofPermutationCostBudget {F : Type*} (costs : FieldOperationCosts) (access : ℕ)
    (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ))) (stride : ℕ) : ℕ :=
  sets.length * (3 * access + costs.add + costs.negate + costs.multiply + 12) +
    chunks.length * (permutationChunkListCostBudget costs access
      (chunks.map (fun chunk => chunk.2.length)).sum chunks.length stride + 2) +
    20 * access + 30 * (costs.add + costs.negate + costs.multiply + 1)

/-- A common lookup budget derived from all stored lookup expression nodes and list cells. -/
def subProofLookupCostBudget {F : Type*} (costs : FieldOperationCosts) (node access : ℕ)
    (lookups : List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F))) : ℕ :=
  let nodes := (lookups.map (fun lookup =>
    (lookup.2.1.map exprNodeCount).sum + (lookup.2.2.map exprNodeCount).sum)).sum
  let width := (lookups.map (fun lookup => lookup.2.1.length + lookup.2.2.length)).sum
  2 * (nodes * (node + 1 + access + costs.add + costs.negate + costs.multiply) +
    width * (access + costs.multiply + costs.add + 2) + 2) +
    50 * access + 100 * (costs.add + costs.negate + costs.multiply + 1)

/-- One lookup's complete cost is bounded by the actual aggregate input sizes. -/
theorem lookupExpressionsCosted_cost_le_aggregate {F : Type*} [CommRing F]
    (costs : FieldOperationCosts) (node access : ℕ)
    (lookups : List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F)))
    (lookup : LookupEval (F × ℕ) × List (Expr F) × List (Expr F)) (hmem : lookup ∈ lookups)
    (fixed advice instanceRead : ℕ → F × ℕ) (theta beta gamma l0 lLast lBlind : F × ℕ)
    (hle : lookupEvalReadBound lookup.1 access)
    (hfixed : ∀ index, (fixed index).2 ≤ access) (hadvice : ∀ index, (advice index).2 ≤ access)
    (hinstance : ∀ index, (instanceRead index).2 ≤ access)
    (htheta : theta.2 ≤ access) (hbeta : beta.2 ≤ access) (hgamma : gamma.2 ≤ access)
    (hl0 : l0.2 ≤ access) (hlLast : lLast.2 ≤ access) (hlBlind : lBlind.2 ≤ access) :
    (lookupExpressionsCosted costs node lookup.1 lookup.2.1 lookup.2.2 fixed advice instanceRead
      theta beta gamma l0 lLast lBlind).2 ≤ subProofLookupCostBudget costs node access lookups := by
  let nodes := (lookups.map (fun lookup =>
    (lookup.2.1.map exprNodeCount).sum + (lookup.2.2.map exprNodeCount).sum)).sum
  let width := (lookups.map (fun lookup => lookup.2.1.length + lookup.2.2.length)).sum
  have hnodes : (lookup.2.1.map exprNodeCount).sum + (lookup.2.2.map exprNodeCount).sum ≤ nodes :=
    listValue_le_map_sum (fun entry =>
      (entry.2.1.map exprNodeCount).sum + (entry.2.2.map exprNodeCount).sum) lookups lookup hmem
  have hwidth : lookup.2.1.length + lookup.2.2.length ≤ width :=
    listValue_le_map_sum (fun entry => entry.2.1.length + entry.2.2.length) lookups lookup hmem
  have hpart (expressions : List (Expr F)) (hnodesPart : (expressions.map exprNodeCount).sum ≤ nodes)
      (hwidthPart : expressions.length ≤ width) :
      lookupCompressionCostBudget costs node access expressions ≤
        nodes * (node + 1 + access + costs.add + costs.negate + costs.multiply) +
          width * (access + costs.multiply + costs.add + 2) + 2 := by
    unfold lookupCompressionCostBudget
    gcongr
  have hinput := hpart lookup.2.1 (by omega) (by omega)
  have htable := hpart lookup.2.2 (by omega) (by omega)
  have h := lookupExpressionsCosted_cost_le costs node lookup.1 lookup.2.1 lookup.2.2
    fixed advice instanceRead theta beta gamma l0 lLast lBlind access hle hfixed hadvice hinstance
    htheta hbeta hgamma hl0 hlLast hlBlind
  change _ ≤ 2 * (nodes * (node + 1 + access + costs.add + costs.negate + costs.multiply) +
    width * (access + costs.multiply + costs.add + 2) + 2) +
    50 * access + 100 * (costs.add + costs.negate + costs.multiply + 1)
  omega

/-- Complete sub-proof budget expressed using actual materialized input sizes. -/
def subProofConstraintCostBudget {F : Type*} (costs : FieldOperationCosts) (node access : ℕ)
    (gates : List (Expr F)) (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (lookups : List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F))) (stride : ℕ) : ℕ :=
  gates.length * ((gates.map exprNodeCount).sum *
      (node + 1 + access + costs.add + costs.negate + costs.multiply) + 1) + 1 +
    subProofPermutationCostBudget costs access sets chunks stride +
    (lookups.length * (subProofLookupCostBudget costs node access lookups + 7) + 1) +
    2 * gates.length + sets.length + chunks.length + 5

-- Compose the component bounds without expanding their arithmetic implementations.
attribute [local irreducible] lookupExpressionsCosted permutationExpressionsCosted exprEvalCosted
  mapListCosted flatMapListCosted appendListCosted subProofLookupCostBudget subProofPermutationCostBudget

/-- The assembled constraint bound covers all input queries, arithmetic, routing, and list construction. -/
theorem subProofConstraintsCosted_cost_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (node access : ℕ) (fixed advice instanceRead : ℕ → F × ℕ) (gates : List (Expr F))
    (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (lookups : List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ)
    (hfixed : ∀ index, (fixed index).2 ≤ access) (hadvice : ∀ index, (advice index).2 ≤ access)
    (hinstance : ∀ index, (instanceRead index).2 ≤ access)
    (hsets : ∀ set ∈ sets, permSetReadBound set access)
    (hchunks : ∀ chunk ∈ chunks, permSetReadBound chunk.1 access ∧ ∀ pair ∈ chunk.2, pair.2 ≤ access)
    (hlookups : ∀ lookup ∈ lookups, lookupEvalReadBound lookup.1 access)
    (hbeta : beta.2 ≤ access) (hgamma : gamma.2 ≤ access) (hx : x.2 ≤ access) (hdelta : delta.2 ≤ access)
    (htheta : theta.2 ≤ access) (hl0 : l0.2 ≤ access) (hlLast : lLast.2 ≤ access) (hlBlind : lBlind.2 ≤ access) :
    (subProofConstraintsCosted costs node fixed advice instanceRead gates sets chunks lookups
      beta gamma x delta theta chunkLen l0 lLast lBlind).2 ≤
      subProofConstraintCostBudget costs node access gates sets chunks lookups chunkLen := by
  let gateValues := mapListCosted (exprEvalCosted node costs.add costs.negate costs.multiply fixed advice instanceRead) gates
  let permutation := permutationExpressionsCosted costs sets chunks beta gamma x delta chunkLen l0 lLast lBlind
  let lookupValues := flatMapListCosted (fun lookup =>
    lookupExpressionsCosted costs node lookup.1 lookup.2.1 lookup.2.2 fixed advice instanceRead
      theta beta gamma l0 lLast lBlind) lookups
  let initial := appendListCosted gateValues.1 permutation.1
  let result := appendListCosted initial.1 lookupValues.1
  have hgates : gateValues.2 ≤ gates.length * ((gates.map exprNodeCount).sum *
      (node + 1 + access + costs.add + costs.negate + costs.multiply) + 1) + 1 := by
    apply mapListCosted_cost_le
    intro expression hmem
    refine (exprEvalCosted_cost_le node costs.add costs.negate costs.multiply fixed advice instanceRead
      expression access hfixed hadvice hinstance).trans ?_
    exact Nat.mul_le_mul_right _ (listValue_le_map_sum exprNodeCount gates expression hmem)
  have hpermutation : permutation.2 ≤ subProofPermutationCostBudget costs access sets chunks chunkLen := by
    unfold subProofPermutationCostBudget
    apply permutationExpressionsCosted_cost_le
    · exact hsets
    · intro chunk hmem
      exact ⟨(hchunks chunk hmem).1,
        listValue_le_map_sum (fun entry => entry.2.length) chunks chunk hmem, (hchunks chunk hmem).2⟩
    · exact hbeta
    · exact hgamma
    · exact hx
    · exact hdelta
    · exact hl0
    · exact hlLast
    · exact hlBlind
  have hlookupLength (lookup : LookupEval (F × ℕ) × List (Expr F) × List (Expr F)) :
      (lookupExpressionsCosted costs node lookup.1 lookup.2.1 lookup.2.2 fixed advice instanceRead
        theta beta gamma l0 lLast lBlind).1.length ≤ 5 := by
    rw [lookupExpressionsCosted_length]
  have hlookupCost (lookup : LookupEval (F × ℕ) × List (Expr F) × List (Expr F))
      (hmem : lookup ∈ lookups) :
      (lookupExpressionsCosted costs node lookup.1 lookup.2.1 lookup.2.2 fixed advice instanceRead
        theta beta gamma l0 lLast lBlind).2 ≤ subProofLookupCostBudget costs node access lookups :=
    lookupExpressionsCosted_cost_le_aggregate costs node access lookups lookup hmem
      fixed advice instanceRead theta beta gamma l0 lLast lBlind (hlookups lookup hmem)
      hfixed hadvice hinstance htheta hbeta hgamma hl0 hlLast hlBlind
  have hlookup : lookupValues.2 ≤ lookups.length * (subProofLookupCostBudget costs node access lookups + 7) + 1 := by
    have h := flatMapListCosted_cost_le_sum (fun lookup =>
      lookupExpressionsCosted costs node lookup.1 lookup.2.1 lookup.2.2 fixed advice instanceRead
        theta beta gamma l0 lLast lBlind) lookups
      (fun _ => subProofLookupCostBudget costs node access lookups) (fun _ => 5)
      hlookupCost (fun lookup _ => hlookupLength lookup)
    simpa using h
  have hgateLength : gateValues.1.length = gates.length := by
    simp only [gateValues, mapListCosted_result, List.length_map]
  have hpermutationLength : permutation.1.length ≤ sets.length + chunks.length + 2 :=
    permutationExpressionsCosted_length_le costs sets chunks beta gamma x delta chunkLen l0 lLast lBlind
  have hinitial : initial.2 = gates.length + 1 := by
    simp only [initial, appendListCosted_cost, hgateLength]
  have hinitialLength : initial.1.length ≤ gates.length + sets.length + chunks.length + 2 := by
    simp only [initial, appendListCosted_result, List.length_append, hgateLength]
    omega
  have hresult : result.2 ≤ gates.length + sets.length + chunks.length + 3 := by
    change (appendListCosted initial.1 lookupValues.1).2 ≤ _
    rw [appendListCosted_cost]
    omega
  change gateValues.2 + permutation.2 + lookupValues.2 + initial.2 + result.2 + 1 ≤ _
  unfold subProofConstraintCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
