import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.ListRoutingCost
import Zcash.Snark.Verifier.Expressions

/-!
# Counted permutation boundary and chaining constraints

The first and last constraints retain empty-list behavior. Chaining retains the
verifier's zero default for an absent last evaluation. The last-set lookup pays
for its complete materialized-list traversal; every field access is retained.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Complete access bounds for a supplied permutation set, including each present optional value. -/
def permSetReadBound {F : Type*} (set : PermSetEval (F × ℕ)) (access : ℕ) : Prop :=
  set.eval.2 ≤ access ∧ set.nextEval.2 ≤ access ∧ ∀ value ∈ set.lastEval, value.2 ≤ access

/-- Read an optional costed field, using the verifier's exact zero default. -/
def optionalFieldCosted {F : Type*} [Zero F] : Option (F × ℕ) → F × ℕ
  | none => (0, 1)
  | some value => (value.1, value.2 + 1)

/-- Optional-value erasure preserves both the present and default branches. -/
theorem optionalFieldCosted_result {F : Type*} [Zero F] (value : Option (F × ℕ)) :
    (optionalFieldCosted value).1 = (value.map Prod.fst).getD 0 := by
  cases value <;> rfl

/-- A missing optional value is still charged for its branch. -/
theorem optionalFieldCosted_cost_le {F : Type*} [Zero F] (value : Option (F × ℕ))
    (access : ℕ) (hvalue : ∀ entry ∈ value, entry.2 ≤ access) :
    (optionalFieldCosted value).2 ≤ access + 1 := by
  cases value with
  | none => simp [optionalFieldCosted]
  | some entry =>
    have h := hvalue entry (by simp)
    simp only [optionalFieldCosted]
    omega

/-- Count the optional initial permutation constraint. -/
def permutationFirstCosted {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ))) (l0 : F × ℕ) : List F × ℕ :=
  match sets with
  | [] => ([], 1)
  | first :: _ =>
    let value := fieldMultiplyCosted costs l0 (fieldSubtractCosted costs (1, 1) first.eval)
    ([value.1], value.2 + 2)

/-- Initial-constraint erasure is the original head-dependent list. -/
theorem permutationFirstCosted_result {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ))) (l0 : F × ℕ) :
    (permutationFirstCosted costs sets l0).1 =
      match (sets.map (PermSetEval.map Prod.fst)).head? with
      | none => []
      | some first => [l0.1 * (1 - first.eval)] := by
  cases sets <;>
    simp only [permutationFirstCosted, fieldMultiplyCosted_result, fieldSubtractCosted_result,
      List.map_nil, List.map_cons, List.head?_nil, List.head?_cons, PermSetEval.map]

/-- The initial boundary contributes at most one materialized value. -/
theorem permutationFirstCosted_length_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ))) (l0 : F × ℕ) :
    (permutationFirstCosted costs sets l0).1.length ≤ 1 := by
  cases sets <;> simp [permutationFirstCosted]

/-- Complete cost of the initial boundary, retaining its field readers. -/
theorem permutationFirstCosted_cost_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ))) (l0 : F × ℕ) (access : ℕ)
    (hsets : ∀ set ∈ sets, permSetReadBound set access) (hl0 : l0.2 ≤ access) :
    (permutationFirstCosted costs sets l0).2 ≤
      2 * access + costs.add + costs.negate + costs.multiply + 6 := by
  cases sets with
  | nil => simp [permutationFirstCosted]
  | cons first rest =>
    have h := (hsets first (by simp)).1
    dsimp only [permutationFirstCosted, fieldMultiplyCosted, fieldSubtractCosted,
      fieldAddCosted, fieldNegateCosted]
    omega

/-- Count last-set traversal and the optional final permutation constraint. -/
def permutationLastCosted {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ))) (lLast : F × ℕ) : List F × ℕ :=
  let last := lastListCosted 1 sets
  match last.1 with
  | none => ([], last.2 + 1)
  | some set =>
    let value := fieldMultiplyCosted costs
      (fieldSubtractCosted costs (fieldMultiplyCosted costs set.eval set.eval) set.eval) lLast
    ([value.1], last.2 + value.2 + 2)

/-- Final-constraint erasure keeps the original last-set selection and square. -/
theorem permutationLastCosted_result {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ))) (lLast : F × ℕ) :
    (permutationLastCosted costs sets lLast).1 =
      match (sets.map (PermSetEval.map Prod.fst)).getLast? with
      | none => []
      | some last => [(last.eval ^ 2 - last.eval) * lLast.1] := by
  simp only [permutationLastCosted, lastListCosted_result, List.getLast?_map]
  cases sets.getLast? <;>
    simp only [Option.map_none, Option.map_some, fieldMultiplyCosted_result,
      fieldSubtractCosted_result, PermSetEval.map, pow_two]

/-- The final boundary contributes at most one materialized value. -/
theorem permutationLastCosted_length_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ))) (lLast : F × ℕ) :
    (permutationLastCosted costs sets lLast).1.length ≤ 1 := by
  simp only [permutationLastCosted]
  split <;> simp

/-- The final boundary includes the entire last-set traversal and all field reads. -/
theorem permutationLastCosted_cost_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (sets : List (PermSetEval (F × ℕ))) (lLast : F × ℕ) (access : ℕ)
    (hsets : ∀ set ∈ sets, permSetReadBound set access) (hlLast : lLast.2 ≤ access) :
    (permutationLastCosted costs sets lLast).2 ≤
      2 * sets.length + 4 * access + costs.add + costs.negate + 2 * costs.multiply + 8 := by
  have hlast := lastListCosted_cost_le 1 sets
  cases hresult : (lastListCosted 1 sets).1 with
  | none =>
    simp only [permutationLastCosted, hresult]
    omega
  | some set =>
    have hmem := List.mem_of_getLast? (by simpa only [lastListCosted_result] using hresult)
    have h := (hsets set hmem).1
    simp only [permutationLastCosted, hresult]
    dsimp only [fieldMultiplyCosted, fieldSubtractCosted, fieldAddCosted, fieldNegateCosted]
    omega

/-- Count a chaining constraint, preserving the optional last-evaluation default. -/
def permutationChainCosted {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (next previous : PermSetEval (F × ℕ)) (l0 : F × ℕ) : F × ℕ :=
  fieldMultiplyCosted costs
    (fieldSubtractCosted costs next.eval (optionalFieldCosted previous.lastEval)) l0

/-- The counted chain is exactly the original difference from the preceding last value. -/
theorem permutationChainCosted_result {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (next previous : PermSetEval (F × ℕ)) (l0 : F × ℕ) :
    (permutationChainCosted costs next previous l0).1 =
      ((next.map Prod.fst).eval - (previous.map Prod.fst).lastEval.getD 0) * l0.1 := by
  simp only [permutationChainCosted, fieldMultiplyCosted_result, fieldSubtractCosted_result,
    optionalFieldCosted_result, PermSetEval.map]

/-- Both branches of a chaining constraint retain every input access. -/
theorem permutationChainCosted_cost_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (next previous : PermSetEval (F × ℕ)) (l0 : F × ℕ) (access : ℕ)
    (hnext : permSetReadBound next access) (hprevious : permSetReadBound previous access)
    (hl0 : l0.2 ≤ access) :
    (permutationChainCosted costs next previous l0).2 ≤
      3 * access + costs.add + costs.negate + costs.multiply + 4 := by
  have heval := hnext.1
  have hlast := optionalFieldCosted_cost_le previous.lastEval access hprevious.2.2
  dsimp only [permutationChainCosted, fieldMultiplyCosted, fieldSubtractCosted,
    fieldAddCosted, fieldNegateCosted]
  omega

end Zcash.Snark.ZeroKnowledge
