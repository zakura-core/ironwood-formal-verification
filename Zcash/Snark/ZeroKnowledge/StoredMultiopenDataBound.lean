import Zcash.Snark.ZeroKnowledge.StoredMultiopenDataCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- The stored quotient-prime and final IPA polynomial both retain the fixed commitment capacity. -/
theorem storedMultiopenDataCosted_width (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup)
    (hwidth : ∀ group ∈ groups, group.coefficients.length ≤ 2048) :
    (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 point quotientBlind groups).1.quotientPrime.length ≤ 2048 ∧
      (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 point quotientBlind groups).1.coefficients.length ≤ 2048 := by
  have hq := denseMultiopenFinalCosted_quotient_length_le costs equal read omegaAccess 2 x2 x4 groups 2048 hwidth
  have hp := denseMultiopenFinalCosted_length_le costs equal read omegaAccess 2 x2 x4 groups 2048 hwidth
  unfold storedMultiopenDataCosted
  constructor
  · exact hq
  · exact hp

/-- Complete five-group multi-opening preparation, including real coefficients, inherited blind, and claimed value. -/
def storedMultiopenDataCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess x2Read x4Read pointRead quotientRead : ℕ) : ℕ :=
  denseMultiopenFinalCostBudget costs equal read omegaAccess 2 x2Read x4Read 5 2048 3 +
    storedMultiopenBlindCostBudget costs read x4Read quotientRead 5 +
    (2048 * (pointRead + read + costs.add + costs.multiply + 1) + 1) + 1

/-- Actual five-group dimensions discharge every component of the complete multi-opening preparation cost. -/
theorem storedMultiopenDataCosted_cost_le (costs : FieldOperationCosts) (equal read omegaAccess : ℕ)
    (x2 x4 point quotientBlind : Fp × ℕ) (groups : List StoredOpeningGroup)
    (hlength : groups.length = 5) (hwidth : ∀ group ∈ groups, group.coefficients.length ≤ 2048)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 3) :
    (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 point quotientBlind groups).2 ≤
      storedMultiopenDataCostBudget costs equal read omegaAccess x2.2 x4.2 point.2 quotientBlind.2 := by
  have hf := denseMultiopenFinalCosted_cost_le costs equal read omegaAccess 2 x2 x4 groups 2048 3 hwidth hpoints
  have hb := storedMultiopenBlindCosted_cost_le costs read x4 quotientBlind groups
  have hw : (denseMultiopenFinalCosted costs equal read omegaAccess 2 x2 x4 groups).1.2.length ≤ 2048 :=
    denseMultiopenFinalCosted_length_le costs equal read omegaAccess 2 x2 x4 groups 2048 hwidth
  have hv := listHornerCosted_cost read costs.add costs.multiply point
    (denseMultiopenFinalCosted costs equal read omegaAccess 2 x2 x4 groups).1.2
  have hvb := Nat.add_le_add_right
    (Nat.mul_le_mul_right (point.2 + read + costs.add + costs.multiply + 1) hw) 1
  rewrite [hlength] at hf hb
  unfold storedMultiopenDataCosted
  change (denseMultiopenFinalCosted costs equal read omegaAccess 2 x2 x4 groups).2 +
    (storedMultiopenBlindCosted costs read x4 quotientBlind groups).2 +
      (listHornerCosted read costs.add costs.multiply point
        (denseMultiopenFinalCosted costs equal read omegaAccess 2 x2 x4 groups).1.2).2 + 1 ≤ _
  unfold storedMultiopenDataCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
