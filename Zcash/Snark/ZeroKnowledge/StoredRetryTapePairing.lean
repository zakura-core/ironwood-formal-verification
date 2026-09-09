import Zcash.Snark.ZeroKnowledge.StoredRowsCost

namespace Zcash.Snark.ZeroKnowledge

/-- Pairing equally sized finite stored tapes preserves the original sample indices. -/
theorem zipListCosted_ofFn_result {α β : Type*} {count : ℕ}
    (left : Fin count → α) (right : Fin count → β) :
    (zipListCosted (List.ofFn left) (List.ofFn right)).1 = List.ofFn (fun i => (left i, right i)) := by
  rewrite [zipListCosted_result]
  apply List.ext_getElem
  · simp only [List.length_zip, List.length_ofFn, Nat.min_self]
  · intro index hleft hright
    simp only [List.getElem_zip, List.getElem_ofFn]

/-- Retained finite tape pairing has the requested dimensions, with no independence assumption. -/
theorem zipListCosted_shape {α β : Type*} (left : List (List α)) (right : List (List β))
    (rows leftWidth rightWidth : ℕ) (hl : left.length = rows) (hr : right.length = rows)
    (hleft : ∀ row ∈ left, row.length = leftWidth) (hright : ∀ row ∈ right, row.length = rightWidth) :
    (zipListCosted left right).1.length = rows ∧
      ∀ tape ∈ (zipListCosted left right).1, tape.1.length = leftWidth ∧ tape.2.length = rightWidth := by
  rewrite [zipListCosted_result]
  constructor
  · simp only [List.length_zip, hl, hr, Nat.min_self]
  · intro tape h
    have hm := List.of_mem_zip h
    exact ⟨hleft tape.1 hm.1, hright tape.2 hm.2⟩

end Zcash.Snark.ZeroKnowledge
