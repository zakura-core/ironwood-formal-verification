import Zcash.Snark.ZeroKnowledge.OpeningGroupLayoutCost

namespace Zcash.Snark.ZeroKnowledge

/-- Every member of the counted first group comes from one of its declared providers. -/
theorem firstOpeningGroupCosted_property {α : Type*} {actions : ℕ}
    (instances : Fin actions → α × ℕ) (tables : Fin actions → Fin 3 → α × ℕ)
    (fixed : Fin 29 → α × ℕ) (sigma : Fin 15 → α × ℕ) (quotient linear : α × ℕ)
    (property : α → Prop)
    (hinstances : ∀ action, property (instances action).1)
    (htables : ∀ action index, property (tables action index).1)
    (hfixed : ∀ index, property (fixed index).1) (hsigma : ∀ index, property (sigma index).1)
    (hquotient : property quotient.1) (hlinear : property linear.1) :
    ∀ member ∈ (firstOpeningGroupCosted instances tables fixed sigma quotient linear).1, property member := by
  intro member hmember
  rewrite [firstOpeningGroupCosted_result] at hmember
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.mem_nil_iff, or_false] at hmember
  rcases hmember with ((⟨action, _, rfl | ⟨index, _, rfl⟩⟩ | ⟨index, _, rfl⟩) | ⟨index, _, rfl⟩) | rfl | rfl
  · exact hinstances action
  · exact htables action index
  · exact hfixed index
  · exact hsigma index
  · exact hquotient
  · exact hlinear

end Zcash.Snark.ZeroKnowledge
