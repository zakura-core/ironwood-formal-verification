import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

namespace Zcash.Snark.ZeroKnowledge

/-- Materialize every row of a successful prepared column, retaining preparation and failure costs. -/
def materializeOptionalRowsCosted {α : Type*} {width : ℕ}
    (prepared : Option (Fin width → α × ℕ) × ℕ) : Option (List α) × ℕ :=
  match prepared.1 with
  | none => (none, prepared.2 + 1)
  | some rows =>
      let values := ofFnCosted rows
      (some values.1, prepared.2 + values.2 + 2)

/-- Erasure preserves failure or the complete original finite row vector. -/
theorem materializeOptionalRowsCosted_result {α : Type*} {width : ℕ}
    (prepared : Option (Fin width → α × ℕ) × ℕ) :
    (materializeOptionalRowsCosted prepared).1 =
      prepared.1.map (fun rows => List.ofFn (fun index => (rows index).1)) := by
  cases h : prepared.1 <;> simp only [materializeOptionalRowsCosted, h,
    ofFnCosted_result, Option.map_none, Option.map_some]

/-- Every successful result contains exactly one materialized entry for each row. -/
theorem materializeOptionalRowsCosted_length {α : Type*} {width : ℕ}
    (prepared : Option (Fin width → α × ℕ) × ℕ) (values : List α)
    (hvalues : (materializeOptionalRowsCosted prepared).1 = some values) : values.length = width := by
  cases h : prepared.1 with
  | none => simp only [materializeOptionalRowsCosted, h, reduceCtorEq] at hvalues
  | some rows =>
      simp only [materializeOptionalRowsCosted, h, Option.some.injEq] at hvalues
      rw [← hvalues]
      exact ofFnCosted_length _

/-- The complete materialization bound retains every possible successful row reader. -/
theorem materializeOptionalRowsCosted_cost_le {α : Type*} {width : ℕ}
    (prepared : Option (Fin width → α × ℕ) × ℕ) (rowRead : ℕ)
    (hread : ∀ rows, prepared.1 = some rows → ∀ index, (rows index).2 ≤ rowRead) :
    (materializeOptionalRowsCosted prepared).2 ≤
      prepared.2 + width * (rowRead + 1) + width * width + 3 := by
  cases h : prepared.1 with
  | none => simp only [materializeOptionalRowsCosted, h]; omega
  | some rows =>
      have hv := ofFnCosted_cost_le rows rowRead (hread rows h)
      simp only [materializeOptionalRowsCosted, h]
      omega

end Zcash.Snark.ZeroKnowledge
