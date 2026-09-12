import Zcash.Snark.ZeroKnowledge.OpeningCommitmentVectorCost
import Zcash.Snark.ZeroKnowledge.OpeningScalarVectorsCost
import Zcash.Snark.ZeroKnowledge.OpeningPointSetsCost
import Zcash.Snark.ZeroKnowledge.OpeningEvaluationSetsCost
import Zcash.Snark.ZeroKnowledge.MultiopenCombinationCost

/-!
# Counted complete public multi-opening

This construction includes all public polynomial preparation, commitment and
scalar group reconstruction, point arithmetic, node routing, interpolation, and
the final point/scalar fold. Intermediate vectors are materialized and their
construction costs remain in the total. The quotient evaluation is a supplied
scalar with its complete cost; its calculation is a separate composition layer.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp URS omegaOf)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Compute the entire public opening with its preparation and subsequent arithmetic costs. -/
def plonkPublicOpeningCosted (costs : FieldOperationCosts)
    (groupAdd groupScale equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ)
    (points : Fin (22 * actions + 10) → G × ℕ) (views : List (Fin 5 → Fp × ℕ))
    (x x1 x2 x4 q hEval rEval firstGroup : Fp × ℕ) : (G × Fp) × ℕ :=
  let commitments := openingCommitmentVectorCosted costs groupAdd groupScale equal omegaAccess
    instances fixed sigma generators W x x1 points
  let nodes := openingNodeValuesCosted costs equal read omegaAccess instances fixed sigma views x x1 hEval rEval
  let values := openingGroupValuesCosted (actions := actions) costs equal read views x1 firstGroup
  let pointSets := openingPointSetsCosted costs (omegaOf 11, omegaAccess) x
  let sets := openingEvaluationSetsCosted read pointSets nodes values
  let initial := multiopenEvalCosted costs read x2 q sets.1
  let pointEntries := mapListCosted (fun point => ((point, 1), 2)) commitments.1
  let valueEntries := mapListCosted (fun value => ((value, 1), 2)) values.1
  let quotientPrime := plonkQuotientPrimeEntryCosted points
  let result := multiopenPointFoldCosted costs groupAdd groupScale x4 quotientPrime pointEntries.1 valueEntries.1 initial
  (result.1, commitments.2 + sets.2 + pointEntries.2 + valueEntries.2 + result.2 + 1)

/-- Erasure gives the exact original public opening after evaluating its symbolic MSM. -/
theorem plonkPublicOpeningCosted_result (costs : FieldOperationCosts)
    (groupAdd groupScale equal read omegaAccess : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (U : G)
    (points : Fin (22 * actions + 10) → G × ℕ) (views : List (Fin 5 → Fp × ℕ))
    (x x1 x2 x4 q hEval rEval firstGroup : Fp × ℕ) :
    let urs : URS G := { k := 11, g := fun index => (generators index).1, w := W.1, u := U }
    let pub := plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
      (fun column row => (fixed column row).1) (fun column row => (sigma column row).1)
    let view := ((fun index => (points index).1), views.map (fun column index => (column index).1), rEval.1, firstGroup.1)
    let result := plonkPublicOpening urs pub x.1 x1.1 x2.1 x4.1 q.1 hEval.1 view
    (plonkPublicOpeningCosted costs groupAdd groupScale equal read omegaAccess
      instances fixed sigma generators W points views x x1 x2 x4 q hEval rEval firstGroup).1 =
      (result.1.eval urs, result.2) := by
  let urs : URS G := { k := 11, g := fun index => (generators index).1, w := W.1, u := U }
  let pub := plonkPublicPolynomialsFromRows (fun action row => (instances action row).1)
    (fun column row => (fixed column row).1) (fun column row => (sigma column row).1)
  let rawPoints := fun index => (points index).1
  dsimp only
  unfold plonkPublicOpeningCosted
  dsimp only
  rw [multiopenPointFoldCosted_msm urs]
  simp only [mapListCosted_result, Function.comp_def,
    openingCommitmentVectorCosted_result costs groupAdd groupScale equal omegaAccess
      instances fixed sigma generators W U x x1 points,
    openingGroupValuesCosted_result costs equal read views x1 firstGroup pub x.1 rEval.1 rawPoints,
    multiopenEvalCosted_result, openingEvaluationSetsCosted, ofFnCosted_result,
    openingPointSetsCosted_result,
    openingNodeValuesCosted_result costs equal read omegaAccess instances fixed sigma views
      x x1 hEval rEval rawPoints firstGroup.1,
    openingSetEntryCosted_ofFn, List.map_ofFn, plonkQuotientPrimeEntryCosted_result,
    plonkPublicOpening]
  rfl

end Zcash.Snark.ZeroKnowledge
