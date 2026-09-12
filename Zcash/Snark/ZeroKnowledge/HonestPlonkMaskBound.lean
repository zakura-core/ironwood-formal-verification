import Zcash.Snark.ZeroKnowledge.HonestPlonkMaskSource

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp omegaOf)
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] privatePolynomialCoefficientsCosted rowCoefficientsCosted

/-- Complete real-mask budget: private interpolation, all commitments, all observations, and both mask values. -/
def honestPlonkMaskCostBudget (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale actions rows pieces rowRead generatorRead entryRead
      xRead qRead constantRead slopeRead quotientRead firstRead wRead : ℕ) : ℕ :=
  (rows * (2048 * (rowCoefficientCostBudget costs 2048 rowRead omegaAccess + 1) + 2048 * 2048 + 2) + 1) +
    (constantRead + slopeRead + 3) +
    plonkCommitmentPointsCostBudget equal read groupAdd groupScale actions rows pieces 2048 generatorRead entryRead
      (read + 1) (read + 1) wRead +
    (rows * 3 + 1) +
    (rows * (5 * (publicRowEvaluationCostBudget costs rowRead omegaAccess
      (xRead + omegaAccess + qRead + 7 * (costs.multiply + 1) + costs.inverse + 12) + 1) + 25 + 2) + 1) +
    (2 * (xRead + read + costs.add + costs.multiply + 1) + 1) +
    (2048 * (qRead + read + costs.add + costs.multiply + 1) + 1) + quotientRead + firstRead + 5

/-- The entire materialized real PLONK mask has a bound derived from its actual stored inputs. -/
theorem honestPlonkMaskCosted_cost_le (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (rows : List (Fin 2048 → Fp × ℕ))
    (pieces : List (List Fp)) (quotientPrime firstGroup : List Fp × ℕ)
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x q constant slope : Fp × ℕ)
    (rowRead generatorRead entryRead : ℕ) (hrows : ∀ column ∈ rows, ∀ row, (column row).2 ≤ rowRead)
    (hpieces : ∀ piece ∈ pieces, piece.length ≤ 2048) (hq : quotientPrime.1.length ≤ 2048)
    (hfirst : firstGroup.1.length ≤ 2048) (hg : ∀ i, (generators i).2 ≤ generatorRead)
    (he : ∀ i, (entries i).2 ≤ entryRead) :
    (honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W rows pieces
      quotientPrime firstGroup entries x q constant slope).2 ≤
      honestPlonkMaskCostBudget costs equal read omegaAccess groupAdd groupScale actions rows.length pieces.length
        rowRead generatorRead entryRead x.2 q.2 constant.2 slope.2 quotientPrime.2 firstGroup.2 W.2 := by
  let columns := privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows
  let linear := denseLinearMaskCosted constant slope
  let points := plonkCommitmentPointsCosted equal read groupAdd groupScale generators W columns.1 pieces
    (linear.1, read + 1) (quotientPrime.1, read + 1) entries
  let observations := observeColumnRowsCosted costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) x q) rows
  have hcolumns := privatePolynomialCoefficientsCosted_cost_le costs (omegaOf 11, omegaAccess) rows rowRead hrows
  have hw (poly : List Fp) (hpoly : poly ∈ columns.1) : poly.length ≤ 2048 :=
    (privatePolynomialCoefficientsCosted_width costs (omegaOf 11, omegaAccess) rows poly hpoly).le
  have hpoints := plonkCommitmentPointsCosted_cost_le equal read groupAdd groupScale generators W columns.1 pieces
    (linear.1, read + 1) (quotientPrime.1, read + 1) entries 2048 generatorRead entryRead hw hpieces (by change 2 ≤ 2048; decide) hq hg he
  have hclen : columns.1.length = rows.length := privatePolynomialCoefficientsCosted_length costs (omegaOf 11, omegaAccess) rows
  change points.2 ≤ plonkCommitmentPointsCostBudget equal read groupAdd groupScale actions columns.1.length pieces.length
    2048 generatorRead entryRead (read + 1) (read + 1) W.2 at hpoints
  rewrite [hclen] at hpoints
  have hobs := observeColumnRowsCosted_cost_le costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) x q) rows
  have hobsRead := observeColumnRowsCosted_readBound costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) x q) rows rowRead
    (x.2 + omegaAccess + q.2 + 7 * (costs.multiply + 1) + costs.inverse + 12) hrows
    (observationPointCosted_cost_le costs (omegaOf 11, omegaAccess) x q)
  have hm := materializeRowsCosted_cost_le observations.1
    (publicRowEvaluationCostBudget costs rowRead omegaAccess
      (x.2 + omegaAccess + q.2 + 7 * (costs.multiply + 1) + costs.inverse + 12)) hobsRead
  have holen : observations.1.length = rows.length := observeColumnRowsCosted_length costs omegaAccess
    (observationPointCosted costs (omegaOf 11, omegaAccess) x q) rows
  rewrite [holen] at hm
  change (materializeRowsCosted observations.1).2 ≤ rows.length * (5 *
    (publicRowEvaluationCostBudget costs rowRead omegaAccess
      (x.2 + omegaAccess + q.2 + 7 * (costs.multiply + 1) + costs.inverse + 12) + 1) + 25 + 2) + 1 at hm
  have hl := listHornerCosted_cost read costs.add costs.multiply x linear.1
  have hllen : linear.1.length = 2 := denseLinearMaskCosted_length constant slope
  rewrite [hllen] at hl
  have hfv : (listHornerCosted read costs.add costs.multiply q firstGroup.1).2 ≤
      2048 * (q.2 + read + costs.add + costs.multiply + 1) + 1 := by
    rewrite [listHornerCosted_cost]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hfirst) 1
  have hlinear : linear.2 = constant.2 + slope.2 + 3 := rfl
  change columns.2 ≤ rows.length * (2048 * (rowCoefficientCostBudget costs 2048 rowRead omegaAccess + 1) +
    2048 * 2048 + 2) + 1 at hcolumns
  change observations.2 ≤ rows.length * 3 + 1 at hobs
  unfold honestPlonkMaskCosted
  change columns.2 + linear.2 + points.2 + observations.2 + (materializeRowsCosted observations.1).2 +
    (listHornerCosted read costs.add costs.multiply x linear.1).2 +
      (listHornerCosted read costs.add costs.multiply q firstGroup.1).2 + quotientPrime.2 + firstGroup.2 + 5 ≤ _
  unfold honestPlonkMaskCostBudget
  omega

end Zcash.Snark.ZeroKnowledge
