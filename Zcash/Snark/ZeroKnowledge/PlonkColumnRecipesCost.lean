import Zcash.Snark.ZeroKnowledge.PrivateColumnOrderCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic

/-- Materialize the original private-column order with each column's exact masking boundary. -/
def privateColumnRecipesCosted (actions : ℕ) : List (PrivateColumnId actions × ℕ) × ℕ :=
  let ids := privateColumnOrderCosted actions
  let recipes := mapListCosted (fun id => ((id, id.firstMasked), 6)) ids.1
  (recipes.1, ids.2 + recipes.2 + 1)

/-- Recipe construction preserves the original identifier and mask-boundary sequence. -/
theorem privateColumnRecipesCosted_result (actions : ℕ) :
    (privateColumnRecipesCosted actions).1 =
      (privateColumnOrder actions).map (fun id => (id, id.firstMasked)) := by
  simp only [privateColumnRecipesCosted, mapListCosted_result, privateColumnOrderCosted_result]

/-- There is exactly one recipe for each of the 22 private columns per Action. -/
theorem privateColumnRecipesCosted_length (actions : ℕ) :
    (privateColumnRecipesCosted actions).1.length = 22 * actions := by
  simp only [privateColumnRecipesCosted_result, List.length_map, privateColumnOrder_length]

/-- Installing any retained-row constructor gives exactly the existing private-column steps. -/
theorem privateColumnRecipesCosted_steps {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → Fin 2048 → Fp) :
    (privateColumnRecipesCosted actions).1.map
        (fun recipe => (⟨recipe.2, construct recipe.1⟩ : ColumnStep 2048)) =
      plonkColumnSteps construct := by
  simp only [privateColumnRecipesCosted_result, List.map_map, Function.comp_def, plonkColumnSteps]

/-- Every schedule allocation, append, and mask-kind case is included in the preparation bound. -/
theorem privateColumnRecipesCosted_cost_le (actions : ℕ) :
    (privateColumnRecipesCosted actions).2 ≤ 4 * actions * actions + 414 * actions + 12 := by
  have hi := privateColumnOrderCosted_cost_le actions
  have hm := mapListCosted_cost_le (fun id : PrivateColumnId actions => ((id, id.firstMasked), 6))
    (privateColumnOrderCosted actions).1 6 (fun _ _ => le_rfl)
  rw [privateColumnOrderCosted_length] at hm
  simp only [privateColumnRecipesCosted]
  omega

end Zcash.Snark.ZeroKnowledge
