import Zcash.Snark.ZeroKnowledge.FieldExponentCost
import Zcash.Snark.Verifier.Assemble

/-!
# Counted verifier domain-basis values

The counted implementation preserves the exact totalized formulas used by the
verifier at every challenge. It includes signed powers, the natural field cast,
all inversions and field operations, and the full sum over blinding rotations.
No nonzero-denominator or off-domain premise is used.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Compute one domain-basis value with explicit costs for all of its arithmetic. -/
def lagrangeBasisValueCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (omega : F × ℕ) (n : ℕ) (xn x : F × ℕ) (index : ℤ) : F × ℕ :=
  let power := fieldIntegerPowerCosted costs omega index
  let width := fieldNatCastCosted costs.add n
  fieldDivideCosted costs
    (fieldMultiplyCosted costs (fieldSubtractCosted costs xn (1, 1)) power)
    (fieldMultiplyCosted costs width (fieldSubtractCosted costs x power))

/-- The counted formula gives exactly the verifier's domain-basis value. -/
theorem lagrangeBasisValueCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (omega : F × ℕ) (n : ℕ) (xn x : F × ℕ) (index : ℤ) :
    (lagrangeBasisValueCosted costs omega n xn x index).1 =
      lagrangeBasisValue omega.1 n xn.1 x.1 index := by
  simp only [lagrangeBasisValueCosted, fieldDivideCosted_result, fieldMultiplyCosted_result,
    fieldSubtractCosted_result, fieldIntegerPowerCosted_result, fieldNatCastCosted_result,
    lagrangeBasisValue]

/-- Uniform access budget for one basis value at a bounded signed rotation. -/
def lagrangeBasisValueCostBudget (costs : FieldOperationCosts) (n magnitude access : ℕ) : ℕ :=
  2 * magnitude * (costs.multiply + 1) + n * (costs.add + 1) + 4 * access +
    20 * (costs.add + costs.negate + costs.multiply + costs.inverse + 1)

/-- Signed powering and every denominator operation retain their complete costs. -/
theorem lagrangeBasisValueCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (omega : F × ℕ) (n : ℕ) (xn x : F × ℕ) (index : ℤ) (access : ℕ)
    (homega : omega.2 ≤ access) (hxn : xn.2 ≤ access) (hx : x.2 ≤ access) :
    (lagrangeBasisValueCosted costs omega n xn x index).2 ≤
      lagrangeBasisValueCostBudget costs n index.natAbs access := by
  have hpower := fieldIntegerPowerCosted_cost_le costs omega index
  have hwidth := fieldNatCastCosted_cost (F := F) costs.add n
  dsimp only [lagrangeBasisValueCosted, fieldDivideCosted, fieldMultiplyCosted,
    fieldSubtractCosted, fieldAddCosted, fieldNegateCosted, fieldInverseCosted,
    lagrangeBasisValueCostBudget]
  have htwice : 2 * index.natAbs * (costs.multiply + 1) =
      2 * (index.natAbs * (costs.multiply + 1)) := by ring
  rw [htwice]
  omega

/-- Materialize all three verifier basis values with a counted sum over the blind rows. -/
def lagrangeBasisCosted {F : Type*} [Field F] (costs : FieldOperationCosts)
    (omega : F × ℕ) (n blinding : ℕ) (xn x : F × ℕ) : (F × F × F) × ℕ :=
  let first := lagrangeBasisValueCosted costs omega n xn x 0
  let last := lagrangeBasisValueCosted costs omega n xn x (-((blinding : ℤ) + 1))
  let blind := sumFinCosted costs.add (count := blinding) fun index =>
    lagrangeBasisValueCosted costs omega n xn x (-((index.val : ℤ) + 1))
  ((first.1, last.1, blind.1), first.2 + last.2 + blind.2 + 1)

/-- The complete materialized result is the verifier's original three-value calculation. -/
theorem lagrangeBasisCosted_result {F : Type*} [Field F] (costs : FieldOperationCosts)
    (omega : F × ℕ) (n blinding : ℕ) (xn x : F × ℕ) :
    (lagrangeBasisCosted costs omega n blinding xn x).1 =
      lagrangeBasis omega.1 n blinding xn.1 x.1 := by
  simp only [lagrangeBasisCosted, sumFinCosted_result, lagrangeBasisValueCosted_result, lagrangeBasis]
  congr 2
  rw [← List.sum_ofFn, ← List.sum_eq_foldl]
  apply congrArg List.sum
  refine List.ext_getElem (by simp) ?_
  intro index hleft hright
  simp [← List.map_eq_flatMap]

/-- Complete budget for the two boundary values and every blind-row contribution. -/
theorem lagrangeBasisCosted_cost_le {F : Type*} [Field F] (costs : FieldOperationCosts)
    (omega : F × ℕ) (n blinding : ℕ) (xn x : F × ℕ) (access : ℕ)
    (homega : omega.2 ≤ access) (hxn : xn.2 ≤ access) (hx : x.2 ≤ access) :
    (lagrangeBasisCosted costs omega n blinding xn x).2 ≤
      (blinding + 2) * lagrangeBasisValueCostBudget costs n (blinding + 1) access +
        blinding * (costs.add + 1) + blinding * blinding + 2 := by
  let budget := lagrangeBasisValueCostBudget costs n (blinding + 1) access
  have hvalue (index : ℤ) (hindex : index.natAbs ≤ blinding + 1) :
      (lagrangeBasisValueCosted costs omega n xn x index).2 ≤ budget := by
    refine (lagrangeBasisValueCosted_cost_le costs omega n xn x index access homega hxn hx).trans ?_
    dsimp only [budget, lagrangeBasisValueCostBudget]
    gcongr
  have hfirst := hvalue 0 (by simp)
  have hlast := hvalue (-((blinding : ℤ) + 1)) (by omega)
  have hblind := sumFinCosted_cost_le costs.add (fun index : Fin blinding =>
      lagrangeBasisValueCosted costs omega n xn x (-((index.val : ℤ) + 1))) budget
    (fun index => hvalue _ (by have h := index.isLt; omega))
  dsimp only [lagrangeBasisCosted]
  calc
    _ ≤ budget + budget + (blinding * (budget + costs.add + 1) + blinding * blinding + 1) + 1 := by omega
    _ = _ := by dsimp only [budget]; ring

end Zcash.Snark.ZeroKnowledge
