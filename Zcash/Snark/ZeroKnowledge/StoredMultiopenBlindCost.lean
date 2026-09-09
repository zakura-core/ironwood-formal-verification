import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.StoredOpeningGroup
import Zcash.Snark.ZeroKnowledge.ScalarHornerCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Fold the actual inherited opening-group blinds after the quotient-prime blind. -/
def storedMultiopenBlindCosted (costs : FieldOperationCosts) (read : ℕ)
    (x4 quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup) : Fp × ℕ :=
  let blinds := mapListCosted (fun group => (group.blind, read + 1)) groups
  let result := scalarHornerCosted read costs.add costs.multiply x4 (quotientBlind.1 :: blinds.1)
  (result.1, blinds.2 + result.2 + quotientBlind.2 + 1)

/-- Every inherited blind retains its original Horner weight and position. -/
theorem storedMultiopenBlindCosted_result (costs : FieldOperationCosts) (read : ℕ)
    (x4 quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup) :
    (storedMultiopenBlindCosted costs read x4 quotientBlind groups).1 =
      multiopenFinalBlind x4.1 quotientBlind.1 (groups.map StoredOpeningGroup.erase) := by
  simp only [storedMultiopenBlindCosted, scalarHornerCosted_result, mapListCosted_result,
    multiopenFinalBlind, List.map_map, Function.comp_def, StoredOpeningGroup.erase]

/-- Complete inherited-blind preparation and fold budget. -/
def storedMultiopenBlindCostBudget (costs : FieldOperationCosts)
    (read x4Read quotientRead groups : ℕ) : ℕ :=
  groups * (read + 2) + (groups + 1) * (x4Read + read + costs.add + costs.multiply + 3) + quotientRead + 4

/-- Both storing the blinds and executing the complete final fold are counted. -/
theorem storedMultiopenBlindCosted_cost_le (costs : FieldOperationCosts) (read : ℕ)
    (x4 quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup) :
    (storedMultiopenBlindCosted costs read x4 quotientBlind groups).2 ≤
      storedMultiopenBlindCostBudget costs read x4.2 quotientBlind.2 groups.length := by
  have hb := mapListCosted_cost_le (fun group : StoredOpeningGroup => (group.blind, read + 1)) groups
    (read + 1) (fun _ _ => le_rfl)
  change (mapListCosted (fun group => (group.blind, read + 1)) groups).2 ≤ groups.length * (read + 2) + 1 at hb
  have hf := scalarHornerCosted_cost_le read costs.add costs.multiply x4
    (quotientBlind.1 :: (mapListCosted (fun group => (group.blind, read + 1)) groups).1)
  conv at hf => rhs; simp only [List.length_cons, mapListCosted_result, List.length_map]
  change (mapListCosted (fun group => (group.blind, read + 1)) groups).2 +
    (scalarHornerCosted read costs.add costs.multiply x4
      (quotientBlind.1 :: (mapListCosted (fun group => (group.blind, read + 1)) groups).1)).2 + quotientBlind.2 + 1 ≤ _
  unfold storedMultiopenBlindCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
