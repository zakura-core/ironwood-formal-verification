import Zcash.Snark.ZeroKnowledge.StoredMultiopenValueCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Full actual five-group value budget, including every polynomial evaluation and final fold. -/
def storedMultiopenValueCostBudget (costs : FieldOperationCosts)
    (read x2Read x4Read pointRead width : ℕ) : ℕ :=
  (5 * (storedOpeningSetCostBudget costs read pointRead width 3 + 1) + 1) +
    (5 * (multiopenSetEvalCostBudget costs read 3 3 pointRead (read + 1) +
      x2Read + costs.multiply + costs.add + 4) + 7) +
    (5 * (read + 3) + 1) + (6 * (x4Read + read + costs.add + costs.multiply + 3) + 2) + 2

/-- Actual group dimensions discharge the full verifier-value reconstruction bound. -/
theorem storedMultiopenValueCosted_cost_le (costs : FieldOperationCosts) (read : ℕ)
    (x2 x4 point : Fp × ℕ) (groups : List StoredOpeningGroup) (width : ℕ)
    (hlength : groups.length ≤ 5) (hwidth : ∀ group ∈ groups, group.coefficients.length ≤ width)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 3) :
    (storedMultiopenValueCosted costs read x2 x4 point groups).2 ≤
      storedMultiopenValueCostBudget costs read x2.2 x4.2 point.2 width := by
  let sets := mapListCosted (storedOpeningSetCosted costs read point) groups
  have hslen : sets.1.length ≤ 5 := by
    change (mapListCosted (storedOpeningSetCosted costs read point) groups).1.length ≤ _
    simpa only [mapListCosted_result, List.length_map] using hlength
  have hsets : ∀ entry ∈ sets.1, entry.1.length ≤ 3 ∧ entry.2.1.length ≤ 3 ∧ entry.2.2.2 ≤ read + 1 := by
    intro entry hentry
    change entry ∈ (mapListCosted (storedOpeningSetCosted costs read point) groups).1 at hentry
    simp only [mapListCosted_result, List.mem_map] at hentry
    obtain ⟨group, hgroup, rfl⟩ := hentry
    have h := storedOpeningSetCosted_dimensions costs read point group
    have hp := hpoints group hgroup
    dsimp only at h
    exact ⟨by omega, by omega, by omega⟩
  have hprep : sets.2 ≤ 5 * (storedOpeningSetCostBudget costs read point.2 width 3 + 1) + 1 := by
    have h := mapListCosted_cost_le (storedOpeningSetCosted costs read point) groups
      (storedOpeningSetCostBudget costs read point.2 width 3) (by
        intro group hgroup
        have h := storedOpeningSetCosted_cost_le costs read point group
        refine h.trans ?_
        have hw := hwidth group hgroup
        have hp := hpoints group hgroup
        unfold storedOpeningSetCostBudget
        gcongr)
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlength) 1)
  have hquot := (multiopenEvalCosted_cost_le costs read x2 point sets.1).trans
    (multiopenEvalCostBudget_le_five costs read x2.2 point.2 (read + 1) sets.1 hslen hsets)
  let values := mapListCosted (fun entry : List Fp × List Fp × (Fp × ℕ) => (entry.2.2.1, read + 2)) sets.1
  have hv := mapListCosted_cost_le
    (fun entry : List Fp × List Fp × (Fp × ℕ) => (entry.2.2.1, read + 2)) sets.1 (read + 2) (fun _ _ => le_rfl)
  have hvb : values.2 ≤ 5 * (read + 3) + 1 :=
    hv.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hslen) 1)
  have hvlen : values.1.length ≤ 5 := by
    change (mapListCosted (fun entry : List Fp × List Fp × (Fp × ℕ) => (entry.2.2.1, read + 2)) sets.1).1.length ≤ _
    simpa only [mapListCosted_result, List.length_map] using hslen
  have hf := scalarHornerCosted_cost_le read costs.add costs.multiply x4
    ((multiopenEvalCosted costs read x2 point sets.1).1 :: values.1)
  have hfb := Nat.mul_le_mul_right (x4.2 + read + costs.add + costs.multiply + 3)
    (show ((multiopenEvalCosted costs read x2 point sets.1).1 :: values.1).length ≤ 6 by simpa using Nat.add_le_add_right hvlen 1)
  unfold storedMultiopenValueCosted
  change sets.2 + (multiopenEvalCosted costs read x2 point sets.1).2 + values.2 +
    (scalarHornerCosted read costs.add costs.multiply x4
      ((multiopenEvalCosted costs read x2 point sets.1).1 :: values.1)).2 + 2 ≤ _
  unfold storedMultiopenValueCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
