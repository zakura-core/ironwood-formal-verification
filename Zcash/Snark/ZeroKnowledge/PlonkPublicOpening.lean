import Zcash.Snark.ZeroKnowledge.PlonkCommitments

/-!
# Reconstructing the IPA input from the public pre-IPA view

All group commitments and claimed evaluations below are functions of public polynomials,
challenges, and the enriched pre-IPA view. The only inferred scalar is `H_x(x)`: it is
supplied by a public evaluation function, whose agreement with the honest quotient remains
an explicit premise. The implementation's PLONK constraint calculation must discharge it.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS Msm)
open CompPoly

section CommitmentGroups

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Reconstruct `H_x`'s commitment by weighting the eight emitted quotient-piece points. -/
def plonkCollapsedQuotientPoint {actions : ℕ} (x : Fp)
    (points : Fin (22 * actions + 10) → G) : G :=
  ∑ j : Fin 8, x ^ (2048 * j.val) • plonkPieceEntry points j

/-- Each group's commitment members in the pinned Horner order, using only public points. -/
def plonkPublicCommitmentMembers {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x : Fp) (points : Fin (22 * actions + 10) → G) : Fin 5 → List G :=
  Fin.cons
    ((List.finRange actions).flatMap (fun a =>
      [polynomialCommitment urs.g urs.w (pub.instances a) 1] ++
        (List.finRange 3).map (fun l => plonkColumnEntry points (.lookupTable a l))) ++
      (List.finRange 29).map (fun j => polynomialCommitment urs.g urs.w (pub.fixed (plonkFixedQueryOrder j)) 1) ++
      (List.finRange 15).map (fun j => polynomialCommitment urs.g urs.w (pub.sigma j) 1) ++
      [plonkCollapsedQuotientPoint x points, plonkLinearEntry points])
    (fun i => (plonkPrivateGroupMembers actions i).map (plonkColumnEntry points))

/-- The public member lists are the commitments of the actual polynomial/blind pairs. -/
theorem plonkPublicCommitmentMembers_honest {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (rows : ColumnHistory 2048)
    (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp) (i : Fin 5) :
    plonkPublicCommitmentMembers urs pub x
        (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds).1 i =
      (plonkOpeningPairs pub rows x (pieces rows) coefficients (plonkCommitmentBlindsFromVector blinds) i).map
        (fun pair => polynomialCommitment urs.g urs.w pair.1 pair.2) := by
  let view := honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds
  have hcolumn (id : PrivateColumnId actions) : plonkColumnEntry view.1 id =
      polynomialCommitment urs.g urs.w (privateColumnPolynomial rows id) (plonkColumnEntry blinds id) := by
    change polynomialCommitment urs.g urs.w
      (plonkColumnEntry (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients) id)
      (plonkColumnEntry blinds id) = _
    rw [plonkCommitmentPolynomials_column]
  have hlinear : plonkLinearEntry view.1 =
      polynomialCommitment urs.g urs.w (linearMaskPolynomial coefficients) (plonkLinearEntry blinds) := by
    change polynomialCommitment urs.g urs.w
      (plonkLinearEntry (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients))
      (plonkLinearEntry blinds) = _
    rw [plonkCommitmentPolynomials_linear]
  have hpiece (j : Fin 8) : plonkPieceEntry view.1 j =
      polynomialCommitment urs.g urs.w (pieces rows j) (plonkPieceEntry blinds j) := by
    change polynomialCommitment urs.g urs.w
      (plonkPieceEntry (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients) j)
      (plonkPieceEntry blinds j) = _
    rw [plonkCommitmentPolynomials_piece]
  have hcollapsed : plonkCollapsedQuotientPoint x view.1 =
      polynomialCommitment urs.g urs.w (plonkCollapsedQuotient x (pieces rows))
        (plonkCollapsedQuotientBlind x (plonkPieceEntry blinds)) := by
    rw [plonkCollapsedQuotientPoint]
    simp_rw [hpiece]
    exact (plonkCollapsedQuotient_commitment urs.g urs.w x (pieces rows) (plonkPieceEntry blinds)).symm
  change plonkPublicCommitmentMembers urs pub x view.1 i = _
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [plonkPublicCommitmentMembers, plonkOpeningPairs, plonkCommitmentBlindsFromVector,
      hcolumn, hlinear, hcollapsed, List.map_flatMap, Function.comp_def]
  · simp [plonkPublicCommitmentMembers, plonkOpeningPairs, plonkCommitmentBlindsFromVector,
      hcolumn, Function.comp_def]

/-- Reconstruct all five collapsed commitments from their emitted members. -/
def plonkPublicGroupCommitments {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 : Fp) (points : Fin (22 * actions + 10) → G) : Fin 5 → G :=
  fun i => commitmentHornerFold x1 (plonkPublicCommitmentMembers urs pub x points i)

/-- The reconstructed group points use the same inherited blinds as the honest polynomials. -/
theorem plonkPublicGroupCommitments_honest {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (rows : ColumnHistory 2048)
    (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp) (i : Fin 5) :
    let group := plonkBlindedOpeningGroup pub rows x x1 (pieces rows) coefficients
      (plonkCommitmentBlindsFromVector blinds) i
    plonkPublicGroupCommitments urs pub x x1
        (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds).1 i =
      polynomialCommitment urs.g urs.w group.polynomial group.blind := by
  rw [plonkPublicGroupCommitments, plonkPublicCommitmentMembers_honest]
  exact (plonkBlindedOpeningGroup_commitment urs.g urs.w pub rows x x1 (pieces rows) coefficients
    (plonkCommitmentBlindsFromVector blinds) i).symm

end CommitmentGroups

/-- Scalar claims for the first group at its sole node `x`, ending in inferred `H_x(x)` and `r(x)`. -/
def plonkFirstGroupClaims {actions : ℕ} (pub : PlonkPublicPolynomials actions) (x : Fp)
    (column : PrivateColumnId actions → Fin 5 → Fp) (hEval rEval : Fp) : List Fp :=
  (List.finRange actions).flatMap (fun a =>
    [(pub.instances a).eval x] ++ (List.finRange 3).map (fun l => column (.lookupTable a l) 0)) ++
  (List.finRange 29).map (fun j => (pub.fixed (plonkFixedQueryOrder j)).eval x) ++
  (List.finRange 15).map (fun j => (pub.sigma j).eval x) ++ [hEval, rEval]

/-- Reconstruct every group's node values from the column observations and one inferred scalar. -/
def plonkPublicNodeValues {actions : ℕ} {G : Type*} (pub : PlonkPublicPolynomials actions)
    (x x1 hEval : Fp) (view : PreIpaMaskView 5 (22 * actions + 10) G) : Fin 5 → List Fp :=
  Fin.cons [plonkScalarFold x1 (plonkFirstGroupClaims pub x (privateColumnView view.2.1) hEval view.2.2.1)]
    (fun i => (plonkOpeningPointIndices i.succ).map fun j =>
      plonkScalarFold x1 ((plonkPrivateGroupMembers actions i).map fun id => privateColumnView view.2.1 id j))

section PublicOpening

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Given the inferred quotient value, all reconstructed node claims are actual group evaluations. -/
theorem plonkPublicNodeValues_honest {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 q hEval : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (rows : ColumnHistory 2048)
    (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp)
    (hquotient : (plonkCollapsedQuotient x (pieces rows)).eval x = hEval) (i : Fin 5) :
    plonkPublicNodeValues pub x x1 hEval
        (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds) i =
      (plonkOpeningPointSets (omegaOf 11) x i).map
        (fun point => (plonkOpeningPolynomials pub rows x x1 (pieces rows) coefficients i).eval point) := by
  let view := honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds
  have hcolumn (id : PrivateColumnId actions) (j : Fin 5) : privateColumnView view.2.1 id j =
      (privateColumnPolynomial rows id).eval (plonkObservationPoints (omegaOf 11) x q j) :=
    privateColumnView_observe rows _ id j
  have hlinear : view.2.2.1 = (linearMaskPolynomial coefficients).eval x := by
    simp [view, honestPlonkMaskView, honestPreIpaMaskView, linearMaskView, addSecondEquiv,
      linearMaskPair, linearMaskPolynomial, mul_comm]
  change plonkPublicNodeValues pub x x1 hEval view i = _
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [plonkPublicNodeValues, plonkFirstGroupClaims, plonkOpeningPointSets,
      plonkOpeningPolynomials, plonkOpeningGroups, plonkPolynomialFold_eval,
      plonkFirstGroupPrefix, hcolumn, hlinear, hquotient, plonkObservationPoints,
      List.map_flatMap, List.append_assoc, Function.comp_def]
  · rw [plonkPublicNodeValues, Fin.cons_succ, plonkOpeningPointSets_eq_map (omegaOf 11) x q]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro pointIndex _
    simp [plonkOpeningPolynomials, plonkPolynomialFold_eval, plonkOpeningGroups,
      hcolumn, Function.comp_def]

/-- Apply the existing verifier's reconstruction operations to the public pre-IPA view. -/
def plonkPublicOpening {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q hEval : Fp) (view : PreIpaMaskView 5 (22 * actions + 10) G) :
    Msm urs.k Fp G × Fp :=
  let values := (plonkPreIpaProjection pub x x1 view).groupValues
  let nodes := plonkPublicNodeValues pub x x1 hEval view
  multiopenCombine x4 (plonkQuotientPrimeEntry view.1)
    (List.ofFn fun i => (Msm.zero urs.k Fp G).appendTerm 1 (plonkPublicGroupCommitments urs pub x x1 view.1 i))
    (List.ofFn values)
    (multiopenEval x2 q (List.ofFn fun i => (plonkOpeningPointSets (omegaOf 11) x i, nodes i, values i)))
    (Msm.zero urs.k Fp G)

/-- The opening reconstructed from the public view equals the honest polynomial construction. -/
theorem plonkPublicOpening_honest {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 x4 q hEval : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (rows : ColumnHistory 2048)
    (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp)
    (hquotient : (plonkCollapsedQuotient x (pieces rows)).eval x = hEval) :
    plonkPublicOpening urs pub x x1 x2 x4 q hEval
        (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds) =
      computedMultiopenOpening urs x2 x4 q (plonkQuotientPrimeEntry blinds)
        (plonkBlindedOpeningGroups pub rows x x1 (pieces rows) coefficients
          (plonkCommitmentBlindsFromVector blinds)) := by
  have hprime : plonkQuotientPrimeEntry
        (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds).1 =
      polynomialCommitment urs.g urs.w
        (multiopenQuotientPolynomial x2 (plonkPolynomialOpeningGroups pub rows x x1 (pieces rows) coefficients))
        (plonkQuotientPrimeEntry blinds) := by
    change polynomialCommitment urs.g urs.w
      (plonkQuotientPrimeEntry (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients))
      (plonkQuotientPrimeEntry blinds) = _
    rw [plonkCommitmentPolynomials_quotientPrime]
  simp only [plonkPublicOpening, computedMultiopenOpening, hprime,
    plonkPolynomialOpeningGroups, honestPlonkMaskView_groupValues,
    plonkPublicGroupCommitments_honest, plonkPublicNodeValues_honest _ _ _ _ _ _ _ _ _ _ _ hquotient,
    plonkBlindedOpeningGroups, List.map_ofFn, Function.comp_def, multiopenGroupMsm,
    plonkBlindedOpeningGroup, PolynomialOpeningGroup.forVerifier, PolynomialOpeningGroup.values]

/-- A public algorithm for the IPA input; the quotient evaluation function receives only disclosed values. -/
def plonkPublicIpaInput {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G) : IpaPublic urs.k Fp G :=
  let opened := plonkPublicOpening urs pub x x1 x2 x4 q (expectedHx (privateColumnView view.2.1)) view
  IpaPublic.ofMsm urs opened.1 q opened.2 xi z rounds

/-- The public algorithm reconstructs precisely the IPA input of the honest polynomial computation. -/
theorem plonkPublicIpaInput_honest {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (rows : ColumnHistory 2048)
    (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp)
    (hquotient : (plonkCollapsedQuotient x (pieces rows)).eval x =
      expectedHx (privateColumnView (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x q) rows))) :
    plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx
        (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds) =
      computedMultiopenIpaPublic urs x2 x4 q xi z (plonkQuotientPrimeEntry blinds) rounds
        (plonkBlindedOpeningGroups pub rows x x1 (pieces rows) coefficients
          (plonkCommitmentBlindsFromVector blinds)) := by
  unfold plonkPublicIpaInput
  simp only [honestPlonkMaskView_columns]
  rw [plonkPublicOpening_honest urs pub x x1 x2 x4 q _ pieces rows coefficients blinds hquotient]
  rfl

end PublicOpening

end Zcash.Snark.ZeroKnowledge
