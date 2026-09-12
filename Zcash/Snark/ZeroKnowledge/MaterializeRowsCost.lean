import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

namespace Zcash.Snark.ZeroKnowledge

/-- Force every entry of every finite row reader into stored lists. -/
def materializeRowsCosted {α : Type*} {width : ℕ} (rows : List (Fin width → α × ℕ)) : List (List α) × ℕ :=
  mapListCosted ofFnCosted rows

/-- The complete matrix has exactly the original reader values in their original order. -/
theorem materializeRowsCosted_result {α : Type*} {width : ℕ} (rows : List (Fin width → α × ℕ)) :
    (materializeRowsCosted rows).1 = (rows.map (fun row i => (row i).1)).map List.ofFn := by
  simp only [materializeRowsCosted, mapListCosted_result, ofFnCosted_result, List.map_map, Function.comp_def]

/-- Full matrix materialization preserves the original number of rows. -/
theorem materializeRowsCosted_length {α : Type*} {width : ℕ} (rows : List (Fin width → α × ℕ)) :
    (materializeRowsCosted rows).1.length = rows.length := by
  simp only [materializeRowsCosted_result, List.length_map]

/-- Every materialized row contains all of its original finite entries. -/
theorem materializeRowsCosted_width {α : Type*} {width : ℕ} (rows : List (Fin width → α × ℕ))
    (row : List α) (hrow : row ∈ (materializeRowsCosted rows).1) : row.length = width := by
  simp only [materializeRowsCosted_result, List.mem_map] at hrow
  obtain ⟨_, _, rfl⟩ := hrow
  exact List.length_ofFn

/-- Count every supplied reader invocation and both levels of stored output. -/
theorem materializeRowsCosted_cost_le {α : Type*} {width : ℕ} (rows : List (Fin width → α × ℕ))
    (access : ℕ) (hr : ∀ row ∈ rows, ∀ i, (row i).2 ≤ access) :
    (materializeRowsCosted rows).2 ≤ rows.length * (width * (access + 1) + width * width + 2) + 1 := by
  exact mapListCosted_cost_le ofFnCosted rows (width * (access + 1) + width * width + 1)
    (fun row hrow => ofFnCosted_cost_le row access (hr row hrow))

end Zcash.Snark.ZeroKnowledge
