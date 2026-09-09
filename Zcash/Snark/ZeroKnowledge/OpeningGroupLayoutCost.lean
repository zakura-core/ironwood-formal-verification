import Zcash.Snark.ZeroKnowledge.PrivateColumnOrderCost
import Zcash.Snark.ZeroKnowledge.PlonkOpening

/-!
# Counted opening-group list construction

The public group contains four entries per Action followed by 29 fixed entries,
15 permutation entries, and two final claims. The other groups use the actual
private-column schedule. Construction counts include provider calls, finite-index
adapters, identifiers, list cells, and append traversals.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Construct the shared public-group layout and retain every supplied member cost. -/
def firstOpeningGroupCosted {α : Type*} {actions : ℕ}
    (instances : Fin actions → α × ℕ) (tables : Fin actions → Fin 3 → α × ℕ)
    (fixed : Fin 29 → α × ℕ) (sigma : Fin 15 → α × ℕ) (quotient linear : α × ℕ) : List α × ℕ :=
  let byAction := flattenFinCosted fun action : Fin actions =>
    let instanceValue := instances action
    let entries := ofFnCosted (tables action)
    (instanceValue.1 :: entries.1, instanceValue.2 + entries.2 + 2)
  let fixedEntries := ofFnCosted fixed
  let sigmaEntries := ofFnCosted sigma
  let first := appendListCosted byAction.1 fixedEntries.1
  let second := appendListCosted first.1 sigmaEntries.1
  let result := appendListCosted second.1 [quotient.1, linear.1]
  (result.1, byAction.2 + fixedEntries.2 + sigmaEntries.2 + quotient.2 + linear.2 +
    first.2 + second.2 + result.2 + 4)

/-- Erasure preserves the original Action-major and public-query order. -/
theorem firstOpeningGroupCosted_result {α : Type*} {actions : ℕ}
    (instances : Fin actions → α × ℕ) (tables : Fin actions → Fin 3 → α × ℕ)
    (fixed : Fin 29 → α × ℕ) (sigma : Fin 15 → α × ℕ) (quotient linear : α × ℕ) :
    (firstOpeningGroupCosted instances tables fixed sigma quotient linear).1 =
      (List.finRange actions).flatMap (fun action =>
        [(instances action).1] ++ (List.finRange 3).map (fun index => (tables action index).1)) ++
      (List.finRange 29).map (fun index => (fixed index).1) ++
      (List.finRange 15).map (fun index => (sigma index).1) ++ [quotient.1, linear.1] := by
  simp only [firstOpeningGroupCosted, appendListCosted_result, flattenFinCosted_result,
    ofFnCosted_result, List.ofFn_eq_map, List.flatMap, List.singleton_append]

/-- The public group has exactly four entries per Action and forty-six shared entries. -/
theorem firstOpeningGroupCosted_length {α : Type*} {actions : ℕ}
    (instances : Fin actions → α × ℕ) (tables : Fin actions → Fin 3 → α × ℕ)
    (fixed : Fin 29 → α × ℕ) (sigma : Fin 15 → α × ℕ) (quotient linear : α × ℕ) :
    (firstOpeningGroupCosted instances tables fixed sigma quotient linear).1.length = 4 * actions + 46 := by
  have hactions := flattenFinCosted_length_eq
    (fun action : Fin actions =>
      ((instances action).1 :: (ofFnCosted (tables action)).1,
        (instances action).2 + (ofFnCosted (tables action)).2 + 2)) 4
    (by intro action; simp only [List.length_cons, ofFnCosted_length])
  simp only [firstOpeningGroupCosted, appendListCosted_result, List.length_append,
    ofFnCosted_length, List.length_cons, List.length_nil, hactions]
  omega

/-- Full layout cost includes all member production and all three list concatenations. -/
theorem firstOpeningGroupCosted_cost_le {α : Type*} {actions : ℕ}
    (instances : Fin actions → α × ℕ) (tables : Fin actions → Fin 3 → α × ℕ)
    (fixed : Fin 29 → α × ℕ) (sigma : Fin 15 → α × ℕ) (quotient linear : α × ℕ)
    (access : ℕ) (hinstances : ∀ action, (instances action).2 ≤ access)
    (htables : ∀ action index, (tables action index).2 ≤ access)
    (hfixed : ∀ index, (fixed index).2 ≤ access) (hsigma : ∀ index, (sigma index).2 ≤ access)
    (hquotient : quotient.2 ≤ access) (hlinear : linear.2 ≤ access) :
    (firstOpeningGroupCosted instances tables fixed sigma quotient linear).2 ≤
      actions * actions + actions * (4 * access + 40) + 50 * access + 1200 := by
  let actionRead := fun action : Fin actions =>
    ((instances action).1 :: (ofFnCosted (tables action)).1,
      (instances action).2 + (ofFnCosted (tables action)).2 + 2)
  have haction (action : Fin actions) : (actionRead action).2 ≤ 4 * access + 15 := by
    have hi := hinstances action
    have ht := ofFnCosted_cost_le (tables action) access (htables action)
    dsimp only [actionRead]
    omega
  have hlength (action : Fin actions) : (actionRead action).1.length = 4 := by
    simp only [actionRead, List.length_cons, ofFnCosted_length]
  have hall := flattenFinCosted_cost_le actionRead (4 * access + 15) 4 haction
    (fun action => (hlength action).le)
  have hsize := flattenFinCosted_length_eq actionRead 4 hlength
  have hf := ofFnCosted_cost_le fixed access hfixed
  have hs := ofFnCosted_cost_le sigma access hsigma
  change (flattenFinCosted actionRead).2 + (ofFnCosted fixed).2 + (ofFnCosted sigma).2 +
    quotient.2 + linear.2 +
    (appendListCosted (flattenFinCosted actionRead).1 (ofFnCosted fixed).1).2 +
    (appendListCosted (appendListCosted (flattenFinCosted actionRead).1 (ofFnCosted fixed).1).1
      (ofFnCosted sigma).1).2 +
    (appendListCosted (appendListCosted (appendListCosted (flattenFinCosted actionRead).1
      (ofFnCosted fixed).1).1 (ofFnCosted sigma).1).1 [quotient.1, linear.1]).2 + 4 ≤ _
  simp only [appendListCosted_cost, appendListCosted_result, List.length_append,
    ofFnCosted_length, hsize]
  nlinarith

/-- Materialize one Action's private-group identifiers, including selection and constructor costs. -/
def privateGroupActionCosted {actions : ℕ} (group : Fin 4) (action : Fin actions) :
    List (PrivateColumnId actions) × ℕ :=
  let members : List (PrivateColumnId actions) :=
    if group = 0 then
      [.advice action 0, .advice action 2, .advice action 3, .advice action 4, .advice action 5,
        .permutationProduct action 2, .lookupProduct action 0, .lookupProduct action 1, .lookupProduct action 2]
    else if group = 1 then
      [.advice action 1, .advice action 6, .advice action 7, .advice action 8, .advice action 9]
    else if group = 2 then [.permutationProduct action 0, .permutationProduct action 1]
    else [.lookupInput action 0, .lookupInput action 1, .lookupInput action 2]
  (members, 24)

/-- Construct one complete private opening group in the original Action-major order. -/
def privateOpeningGroupCosted (actions : ℕ) (group : Fin 4) : List (PrivateColumnId actions) × ℕ :=
  flattenFinCosted (privateGroupActionCosted group)

/-- The constructed identifiers are exactly those used by the original multi-opening. -/
theorem privateOpeningGroupCosted_result (actions : ℕ) (group : Fin 4) :
    (privateOpeningGroupCosted actions group).1 = plonkPrivateGroupMembers actions group := by
  fin_cases group <;>
    simp [privateOpeningGroupCosted, privateGroupActionCosted, flattenFinCosted_result,
      plonkPrivateGroupMembers, List.ofFn_eq_map, List.flatMap]

/-- Every private group has at most nine entries per Action. -/
theorem privateOpeningGroupCosted_length_le (actions : ℕ) (group : Fin 4) :
    (privateOpeningGroupCosted actions group).1.length ≤ 9 * actions := by
  fin_cases group <;>
    simp only [privateOpeningGroupCosted, privateGroupActionCosted, flattenFinCosted_result,
      List.length_flatten, List.map_ofFn, Function.comp_def]
  all_goals simp
  all_goals omega

/-- Full private-group construction cost includes its bounded selector and every copied list cell. -/
theorem privateOpeningGroupCosted_cost_le (actions : ℕ) (group : Fin 4) :
    (privateOpeningGroupCosted actions group).2 ≤ actions * actions + 35 * actions + 1 := by
  have h := flattenFinCosted_cost_le (privateGroupActionCosted (actions := actions) group) 24 9
    (by intro action; rfl)
    (by intro action; fin_cases group <;> simp [privateGroupActionCosted])
  change (flattenFinCosted (privateGroupActionCosted group)).2 ≤ _
  nlinarith

end Zcash.Snark.ZeroKnowledge
