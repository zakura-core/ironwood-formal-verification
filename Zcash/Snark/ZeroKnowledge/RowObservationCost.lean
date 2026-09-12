import Zcash.Snark.ZeroKnowledge.PlonkClaimQueriesCost
import Zcash.Snark.ZeroKnowledge.ColumnSequence

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Build column-observation readers while retaining every future polynomial-evaluation cost. -/
def observeColumnRowsCosted (costs : FieldOperationCosts) (omegaAccess : ℕ) {count : ℕ}
    (points : Fin count → Fp × ℕ) (rows : List (Fin 2048 → Fp × ℕ)) :
    List (Fin count → Fp × ℕ) × ℕ :=
  mapListCosted (fun column =>
    ((fun index => rowPolynomialEvalCosted costs (omegaOf 11, omegaAccess) column (points index)), 2)) rows

/-- Erasure is the original complete row-polynomial observation family. -/
theorem observeColumnRowsCosted_result (costs : FieldOperationCosts) (omegaAccess : ℕ) {count : ℕ}
    (points : Fin count → Fp × ℕ) (rows : List (Fin 2048 → Fp × ℕ)) :
    (observeColumnRowsCosted costs omegaAccess points rows).1.map (fun column index => (column index).1) =
      observeColumnRows (omegaOf 11) (fun index => (points index).1)
        (rows.map (fun column row => (column row).1)) := by
  simp only [observeColumnRowsCosted, mapListCosted_result, List.map_map, Function.comp_def,
    observeColumnRows, rowPolynomialEvalCosted_result costs 11 (by decide) omegaAccess]
  rfl

/-- Reader construction keeps one closure per original private column. -/
theorem observeColumnRowsCosted_length (costs : FieldOperationCosts) (omegaAccess : ℕ) {count : ℕ}
    (points : Fin count → Fp × ℕ) (rows : List (Fin 2048 → Fp × ℕ)) :
    (observeColumnRowsCosted costs omegaAccess points rows).1.length = rows.length := by
  simp only [observeColumnRowsCosted, mapListCosted_result, List.length_map]

/-- Closure construction is linear; polynomial evaluation is charged when the reader is invoked. -/
theorem observeColumnRowsCosted_cost_le (costs : FieldOperationCosts) (omegaAccess : ℕ) {count : ℕ}
    (points : Fin count → Fp × ℕ) (rows : List (Fin 2048 → Fp × ℕ)) :
    (observeColumnRowsCosted costs omegaAccess points rows).2 ≤ rows.length * 3 + 1 :=
  mapListCosted_cost_le _ rows 2 (fun _ _ => le_rfl)

/-- Every generated observation reader carries its complete interpolation and evaluation budget. -/
theorem observeColumnRowsCosted_readBound (costs : FieldOperationCosts) (omegaAccess : ℕ) {count : ℕ}
    (points : Fin count → Fp × ℕ) (rows : List (Fin 2048 → Fp × ℕ))
    (rowRead pointRead : ℕ) (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ rowRead)
    (hpoints : ∀ index, (points index).2 ≤ pointRead)
    (column : Fin count → Fp × ℕ)
    (hcolumn : column ∈ (observeColumnRowsCosted costs omegaAccess points rows).1) (index : Fin count) :
    (column index).2 ≤ publicRowEvaluationCostBudget costs rowRead omegaAccess pointRead := by
  simp only [observeColumnRowsCosted, mapListCosted_result, List.mem_map] at hcolumn
  obtain ⟨values, hvalues, rfl⟩ := hcolumn
  have h := rowPolynomialEvalCosted_cost_le costs (omegaOf 11, omegaAccess) values (points index)
    rowRead (hrows values hvalues)
  refine h.trans ?_
  dsimp only [publicRowEvaluationCostBudget]
  gcongr
  exact hpoints index

end Zcash.Snark.ZeroKnowledge
