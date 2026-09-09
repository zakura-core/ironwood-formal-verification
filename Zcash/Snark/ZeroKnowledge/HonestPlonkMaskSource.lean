import Zcash.Snark.ZeroKnowledge.HonestPlonkMaskCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark CompPoly
open Zcash.Arithmetic (Fp omegaOf URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] privatePolynomialCoefficientsCosted rowCoefficientsCosted rowPolynomial densePolynomial

/-- The counted real mask has exactly the original complete observation on the supplied actual polynomials. -/
theorem honestPlonkMaskCosted_result (costs : FieldOperationCosts)
    (equal read omegaAccess groupAdd groupScale : ℕ) {actions : ℕ}
    (generators : Fin 2048 → G × ℕ) (W : G × ℕ) (U : G) (rows : List (Fin 2048 → Fp × ℕ))
    (pieces : List (List Fp)) (quotientPrime firstGroup : List Fp × ℕ)
    (entries : Fin (22 * actions + 10) → Fp × ℕ) (x q constant slope : Fp × ℕ)
    (pub : PlonkPublicPolynomials actions) (x1 x2 : Fp)
    (sourcePieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (hpieces : ∀ i : Fin 8, densePolynomial (pieces.getD i.val []) =
      sourcePieces (rows.map (fun column row => (column row).1)) i)
    (hquotient : densePolynomial quotientPrime.1 = multiopenQuotientPolynomial x2
      (plonkPolynomialOpeningGroups pub (rows.map (fun column row => (column row).1)) x.1 x1
        (sourcePieces (rows.map (fun column row => (column row).1))) (constant.1, slope.1)))
    (hfirst : densePolynomial firstGroup.1 =
      plonkOpeningPolynomials pub (rows.map (fun column row => (column row).1)) x.1 x1
        (sourcePieces (rows.map (fun column row => (column row).1))) (constant.1, slope.1) 0) :
    (honestPlonkMaskCosted costs equal read omegaAccess groupAdd groupScale generators W rows pieces
      quotientPrime firstGroup entries x q constant slope).1 =
      materializePlonkMaskView (honestPlonkMaskView
        ({ k := 11, g := fun i => (generators i).1, w := W.1, u := U } : URS G)
        pub x.1 x1 x2 q.1 sourcePieces (rows.map (fun column row => (column row).1))
        (constant.1, slope.1) (fun i => (entries i).1)) := by
  let urs : URS G := { k := 11, g := fun i => (generators i).1, w := W.1, u := U }
  let erows := rows.map (fun column row => (column row).1)
  let columns := privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows
  let linear := denseLinearMaskCosted constant slope
  have hpolys (i : Fin (22 * actions + 10)) :
      densePolynomial (plonkCommitmentCoefficientCosted equal read columns.1 pieces
        (linear.1, read + 1) (quotientPrime.1, read + 1) i).1 =
        plonkCommitmentPolynomials pub x.1 x1 x2 sourcePieces erows (constant.1, slope.1) i := by
    change densePolynomial (plonkCommitmentCoefficientCosted equal read
      (privatePolynomialCoefficientsCosted costs (omegaOf 11, omegaAccess) rows).1 pieces
      ((denseLinearMaskCosted constant slope).1, read + 1) (quotientPrime.1, read + 1) i).1 = _
    rewrite [plonkCommitmentCoefficientCosted_from_rows, denseLinearMaskCosted_result]
    have he : (fun i : Fin 8 => densePolynomial (pieces.getD i.val [])) = sourcePieces erows := funext hpieces
    rewrite [he, hquotient]
    rfl
  have hpoints : (plonkCommitmentPointsCosted equal read groupAdd groupScale generators W columns.1 pieces
      (linear.1, read + 1) (quotientPrime.1, read + 1) entries).1 =
      List.ofFn (honestPlonkMaskView urs pub x.1 x1 x2 q.1 sourcePieces erows
        (constant.1, slope.1) (fun i => (entries i).1)).1 := by
    rewrite [plonkCommitmentPointsCosted_result]
    apply congrArg List.ofFn
    funext i
    rewrite [hpolys]
    exact (honestPlonkMaskView_points urs pub x.1 x1 x2 q.1 sourcePieces erows
      (constant.1, slope.1) (fun i => (entries i).1) i).symm
  have hcolumns : (materializeRowsCosted (observeColumnRowsCosted costs omegaAccess
      (observationPointCosted costs (omegaOf 11, omegaAccess) x q) rows).1).1 =
      (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x.1 q.1) erows).map List.ofFn := by
    rewrite [materializeRowsCosted_result, observeColumnRowsCosted_result]
    simp only [observationPointCosted_result]
    rfl
  unfold honestPlonkMaskCosted
  change ((plonkCommitmentPointsCosted equal read groupAdd groupScale generators W columns.1 pieces
    (linear.1, read + 1) (quotientPrime.1, read + 1) entries).1,
    (materializeRowsCosted (observeColumnRowsCosted costs omegaAccess
      (observationPointCosted costs (omegaOf 11, omegaAccess) x q) rows).1).1,
    (listHornerCosted read costs.add costs.multiply x linear.1).1,
    (listHornerCosted read costs.add costs.multiply q firstGroup.1).1) = _
  rewrite [hpoints, hcolumns]
  refine Prod.ext ?_ ?_
  · rfl
  · refine Prod.ext ?_ ?_
    · rfl
    · change ((listHornerCosted read costs.add costs.multiply x (denseLinearMaskCosted constant slope).1).1,
        (listHornerCosted read costs.add costs.multiply q firstGroup.1).1) = _
      simp only [listHornerCosted_densePolynomial_result, denseLinearMaskCosted_result, hfirst]
      exact plonkFirstGroup_linearMaskView pub erows x.1 x1 q.1 (sourcePieces erows) (constant.1, slope.1)

end Zcash.Snark.ZeroKnowledge
