import Zcash.Snark.ZeroKnowledge.PlonkCommitmentPointsCost
import Zcash.Snark.ZeroKnowledge.RowObservationCost
import Zcash.Snark.ZeroKnowledge.MaterializeRowsCost
import Zcash.Snark.ZeroKnowledge.DenseCollapsedQuotientCost
import Zcash.Snark.ZeroKnowledge.DensePolynomialEvaluation
import Zcash.Snark.ZeroKnowledge.OpeningPointSetsCost
import Zcash.Snark.ZeroKnowledge.PlonkMaskSimulatorCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp omegaOf URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Materialize the complete real PLONK mask view from its actual rows and stored opening polynomials. -/
@[irreducible] def honestPlonkMaskCosted (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (rows : List (Fin 2048 → Fp × ℕ))
    (pieces : List (List Fp)) (quotientPrime firstGroup : List Fp × ℕ)
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x q constant slope : Fp × ℕ) :
    (List G × (List (List Fp) × (Fp × Fp))) × ℕ :=
  let columns := privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows
  let linear := denseLinearMaskCosted constant slope
  let points := plonkCommitmentPointsCosted equal read groupAdd groupScale generators W columns.1 pieces
    (linear.1, read + 1) (quotientPrime.1, read + 1) entries
  let observations := observeColumnRowsCosted costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) x q) rows
  let stored := materializeRowsCosted observations.1
  let linearValue := listHornerCosted read costs.add costs.multiply x linear.1
  let firstValue := listHornerCosted read costs.add costs.multiply q firstGroup.1
  ((points.1, stored.1, linearValue.1, firstValue.1), columns.2 + linear.2 + points.2 +
    observations.2 + stored.2 + linearValue.2 + firstValue.2 + quotientPrime.2 + firstGroup.2 + 5)

/-- All output commitments are present in the complete real mask view. -/
theorem honestPlonkMaskCosted_points_length (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (rows : List (Fin 2048 → Fp × ℕ))
    (pieces : List (List Fp)) (quotientPrime firstGroup : List Fp × ℕ)
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x q constant slope : Fp × ℕ) :
    (honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W rows pieces
      quotientPrime firstGroup entries x q constant slope).1.1.length = 22 * actions + 10 := by
  unfold honestPlonkMaskCosted
  exact plonkCommitmentPointsCosted_length equal read groupAdd groupScale generators W
    (privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows).1 pieces
    ((denseLinearMaskCosted constant slope).1, read + 1) (quotientPrime.1, read + 1) entries

/-- The complete real mask keeps every original private column. -/
theorem honestPlonkMaskCosted_columns_length (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (rows : List (Fin 2048 → Fp × ℕ))
    (pieces : List (List Fp)) (quotientPrime firstGroup : List Fp × ℕ)
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x q constant slope : Fp × ℕ) :
    (honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W rows pieces
      quotientPrime firstGroup entries x q constant slope).1.2.1.length = rows.length := by
  unfold honestPlonkMaskCosted
  change (materializeRowsCosted (observeColumnRowsCosted costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) x q) rows).1).1.length = _
  rewrite [materializeRowsCosted_length, observeColumnRowsCosted_length]
  rfl

/-- Every private column has all five original disclosed evaluations. -/
theorem honestPlonkMaskCosted_observations_width (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (rows : List (Fin 2048 → Fp × ℕ))
    (pieces : List (List Fp)) (quotientPrime firstGroup : List Fp × ℕ)
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x q constant slope : Fp × ℕ)
    (column : List Fp) (hcolumn : column ∈
      (honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W rows pieces
        quotientPrime firstGroup entries x q constant slope).1.2.1) : column.length = 5 := by
  unfold honestPlonkMaskCosted at hcolumn
  exact materializeRowsCosted_width _ column hcolumn

end Zcash.Snark.ZeroKnowledge
