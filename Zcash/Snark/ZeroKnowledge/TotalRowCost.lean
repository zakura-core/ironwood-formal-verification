import Zcash.Snark.ZeroKnowledge.OptionalRowCost

namespace Zcash.Snark.ZeroKnowledge

/-- Materialize a complete column, explicitly constructing the zero fallback after a preparation failure. -/
def totalizeOptionalRowsCosted {α : Type*} [Zero α] {width : ℕ}
    (prepared : Option (Fin width → α × ℕ) × ℕ) : List α × ℕ :=
  let result := materializeOptionalRowsCosted prepared
  match result.1 with
  | none =>
      let zeros := ofFnCosted (fun _ : Fin width => ((0 : α), 1))
      (zeros.1, result.2 + zeros.2 + 1)
  | some values => (values, result.2 + 1)

/-- Erasure is the original totalized row function, fully materialized in finite-index order. -/
theorem totalizeOptionalRowsCosted_result {α : Type*} [Zero α] {width : ℕ}
    (prepared : Option (Fin width → α × ℕ) × ℕ) :
    (totalizeOptionalRowsCosted prepared).1 =
      List.ofFn ((prepared.1.map (fun rows index => (rows index).1)).getD 0) := by
  cases h : prepared.1 <;> simp only [totalizeOptionalRowsCosted, materializeOptionalRowsCosted, h,
    ofFnCosted_result, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
  rfl

/-- Every returned column has the full declared width, including the zero fallback. -/
theorem totalizeOptionalRowsCosted_length {α : Type*} [Zero α] {width : ℕ}
    (prepared : Option (Fin width → α × ℕ) × ℕ) :
    (totalizeOptionalRowsCosted prepared).1.length = width := by
  rw [totalizeOptionalRowsCosted_result, List.length_ofFn]

/-- Complete materialization budget, including preparation failures and zero-column allocation. -/
theorem totalizeOptionalRowsCosted_cost_le {α : Type*} [Zero α] {width : ℕ}
    (prepared : Option (Fin width → α × ℕ) × ℕ) (rowRead : ℕ)
    (hread : ∀ rows, prepared.1 = some rows → ∀ index, (rows index).2 ≤ rowRead) :
    (totalizeOptionalRowsCosted prepared).2 ≤
      prepared.2 + width * (rowRead + 3) + 2 * width * width + 6 := by
  cases h : prepared.1 with
  | none =>
      have hz := ofFnCosted_cost_le (fun _ : Fin width => ((0 : α), 1)) 1 (fun _ => le_rfl)
      simp only [totalizeOptionalRowsCosted, materializeOptionalRowsCosted, h]
      nlinarith
  | some rows =>
      have hv := ofFnCosted_cost_le rows rowRead (hread rows h)
      simp only [totalizeOptionalRowsCosted, materializeOptionalRowsCosted, h]
      nlinarith

end Zcash.Snark.ZeroKnowledge
