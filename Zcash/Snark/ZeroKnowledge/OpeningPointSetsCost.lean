import Zcash.Snark.ZeroKnowledge.PrivateOpeningNodesCost
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

/-!
# Counted construction of the actual opening points

The finite observation selector executes the specified field products, inverses,
and sixth power. Each group's original index list then selects and materializes
its nodes. The construction and bounds apply also to exceptional field values.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Compute an original observation point, including its branch and arithmetic costs. -/
def observationPointCosted (costs : FieldOperationCosts) (omega x q : Fp × ℕ)
    (index : Fin 5) : Fp × ℕ :=
  let point := match index.val with
    | 0 => x
    | 1 => fieldMultiplyCosted costs x omega
    | 2 => fieldMultiplyCosted costs x (fieldInverseCosted costs omega)
    | 3 =>
      let power := fieldPowerCosted costs.multiply omega.1 6
      fieldMultiplyCosted costs x (fieldInverseCosted costs (power.1, omega.2 + power.2 + 1))
    | _ => q
  (point.1, point.2 + 7)

/-- The counted point selector is the reference five-point observation vector. -/
theorem observationPointCosted_result (costs : FieldOperationCosts) (omega x q : Fp × ℕ)
    (index : Fin 5) :
    (observationPointCosted costs omega x q index).1 = plonkObservationPoints omega.1 x.1 q.1 index := by
  fin_cases index <;> simp only [observationPointCosted, fieldMultiplyCosted_result,
    fieldInverseCosted_result, fieldPowerCosted_result, plonkObservationPoints]
  all_goals rfl

/-- A uniform point budget pays for the longest branch and all supplied scalar reads. -/
theorem observationPointCosted_cost_le (costs : FieldOperationCosts) (omega x q : Fp × ℕ)
    (index : Fin 5) :
    (observationPointCosted costs omega x q index).2 ≤
      x.2 + omega.2 + q.2 + 7 * (costs.multiply + 1) + costs.inverse + 12 := by
  have hpower := fieldPowerCosted_cost costs.multiply omega.1 6
  fin_cases index <;> simp only [observationPointCosted, fieldMultiplyCosted, fieldInverseCosted] <;> omega

/-- Construct one complete original point set using its counted node-index table. -/
def openingPointSetCosted (costs : FieldOperationCosts) (omega x : Fp × ℕ)
    (group : Fin 5) : List Fp × ℕ :=
  let indices := openingPointIndicesCosted group
  let points := mapListCosted (observationPointCosted costs omega x (0, 1)) indices.1
  (points.1, indices.2 + points.2 + 1)

/-- The counted group contains exactly its original nodes in the original order. -/
theorem openingPointSetCosted_result (costs : FieldOperationCosts) (omega x : Fp × ℕ)
    (group : Fin 5) :
    (openingPointSetCosted costs omega x group).1 = plonkOpeningPointSets omega.1 x.1 group := by
  simp only [openingPointSetCosted, mapListCosted_result, openingPointIndicesCosted_result,
    observationPointCosted_result, plonkOpeningPointSets_eq_map omega.1 x.1 0]

/-- Each constructed group has between one and three nodes. -/
theorem openingPointSetCosted_length (costs : FieldOperationCosts) (omega x : Fp × ℕ)
    (group : Fin 5) :
    0 < (openingPointSetCosted costs omega x group).1.length ∧
      (openingPointSetCosted costs omega x group).1.length ≤ 3 := by
  rw [openingPointSetCosted_result]
  exact plonkOpeningPointSets_length omega.1 x.1 group

/-- Every group pays for its table, all point arithmetic, and all output list cells. -/
theorem openingPointSetCosted_cost_le (costs : FieldOperationCosts) (omega x : Fp × ℕ)
    (group : Fin 5) :
    (openingPointSetCosted costs omega x group).2 ≤
      3 * (x.2 + omega.2 + 7 * (costs.multiply + 1) + costs.inverse + 14) + 18 := by
  have hmap := mapListCosted_cost_le (observationPointCosted costs omega x (0, 1))
    (openingPointIndicesCosted group).1
    (x.2 + omega.2 + 1 + 7 * (costs.multiply + 1) + costs.inverse + 12)
    (fun index _ => observationPointCosted_cost_le costs omega x (0, 1) index)
  have hscaled := Nat.mul_le_mul_right
    (x.2 + omega.2 + 1 + 7 * (costs.multiply + 1) + costs.inverse + 12 + 1)
    (openingPointIndicesCosted_length group).2
  simp only [openingPointSetCosted, openingPointIndicesCosted_cost]
  omega

/-- Materialize all five point sets, retaining every group's construction cost. -/
def openingPointSetsCosted (costs : FieldOperationCosts) (omega x : Fp × ℕ) : List (List Fp) × ℕ :=
  ofFnCosted (openingPointSetCosted costs omega x)

/-- The complete point-set vector is the original fixed five-group vector. -/
theorem openingPointSetsCosted_result (costs : FieldOperationCosts) (omega x : Fp × ℕ) :
    (openingPointSetsCosted costs omega x).1 = List.ofFn (plonkOpeningPointSets omega.1 x.1) := by
  simp only [openingPointSetsCosted, ofFnCosted_result, openingPointSetCosted_result]

/-- The finite vector contains exactly five fully materialized point lists. -/
theorem openingPointSetsCosted_length (costs : FieldOperationCosts) (omega x : Fp × ℕ) :
    (openingPointSetsCosted costs omega x).1.length = 5 := ofFnCosted_length _

/-- Complete point preparation has a constant-size structural bound with explicit primitive costs. -/
theorem openingPointSetsCosted_cost_le (costs : FieldOperationCosts) (omega x : Fp × ℕ) :
    (openingPointSetsCosted costs omega x).2 ≤
      5 * (3 * (x.2 + omega.2 + 7 * (costs.multiply + 1) + costs.inverse + 14) + 19) + 26 := by
  exact ofFnCosted_cost_le _ _ (openingPointSetCosted_cost_le costs omega x)

end Zcash.Snark.ZeroKnowledge
