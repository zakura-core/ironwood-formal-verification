import Zcash.Snark.ZeroKnowledge.PlonkColumns
import Zcash.Snark.ZeroKnowledge.MaskPolynomials
import Mathlib.Data.List.GetD

/-!
# The pinned opening groups as polynomial computations

This module installs the common observation points and exact polynomial ordering from
step 6 of the description. It proves that the four groups without the linear mask are projections
of the column evaluation trace, and that the first group has exactly the additive form
used in the joint linear-mask proof. The supplied quotient pieces may depend on all private
rows; their construction and the validity of their opening remain separate obligations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly

/-- Common observation points: `x`, `xω`, `xω⁻¹`, `xω⁻⁶`, and the later IPA point `q`. -/
def plonkObservationPoints (omega x q : Fp) : Fin 5 → Fp :=
  ![x, x * omega, x * omega⁻¹, x * (omega ^ 6)⁻¹, q]

/-- Read a column by its declared position; a missing column is the zero polynomial. -/
def privateColumnPolynomial {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) : CPoly :=
  (rows.map (rowPolynomial (omegaOf 11))).getD ((privateColumnOrder actions).idxOf id) 0

/-- Read the corresponding column's disclosed evaluations in that same position. -/
def privateColumnView {actions d : ℕ} (views : List (Fin d → Fp))
    (id : PrivateColumnId actions) : Fin d → Fp :=
  views.getD ((privateColumnOrder actions).idxOf id) 0

/-- Column lookup commutes with evaluation, including the totalized missing-column case. -/
theorem privateColumnView_observe {actions d : ℕ} (rows : ColumnHistory 2048)
    (points : Fin d → Fp) (id : PrivateColumnId actions) (i : Fin d) :
    privateColumnView (observeColumnRows (omegaOf 11) points rows) id i =
      (privateColumnPolynomial rows id).eval (points i) := by
  have h := List.getD_map (l := rows.map (rowPolynomial (omegaOf 11)))
    (n := (privateColumnOrder actions).idxOf id) (d := (0 : CPoly))
    (fun poly => fun j : Fin d => poly.eval (points j))
  have hzero : (fun j : Fin d => (0 : CPoly).eval (points j)) = 0 := by ext j; simp
  rw [hzero] at h
  simpa only [privateColumnView, observeColumnRows, privateColumnPolynomial,
    List.map_map, Function.comp_def] using congrFun h i

/-- The scalar Horner convention used throughout the pinned prover. -/
def plonkScalarFold (challenge : Fp) (values : List Fp) : Fp :=
  values.foldl (fun acc value => acc * challenge + value) 0

/-- The same Horner convention on coefficient polynomials. -/
def plonkPolynomialFold (challenge : Fp) (polys : List CPoly) : CPoly :=
  polys.foldl (fun acc poly => acc * CPolynomial.C challenge + poly) 0

/-- Evaluating the polynomial fold gives precisely the scalar fold. -/
theorem plonkPolynomialFold_eval (challenge point : Fp) (polys : List CPoly) :
    (plonkPolynomialFold challenge polys).eval point =
      plonkScalarFold challenge (polys.map fun poly => poly.eval point) := by
  have h (initial : CPoly) :
      (polys.foldl (fun acc poly => acc * CPolynomial.C challenge + poly) initial).eval point =
        (polys.map fun poly => poly.eval point).foldl (fun acc value => acc * challenge + value)
          (initial.eval point) := by
    induction polys generalizing initial with
    | nil => rfl
    | cons poly polys ih => simp [ih]
  simpa only [plonkPolynomialFold, plonkScalarFold, CPolynomial.eval_zero] using h 0

/-- Circuit-fixed public polynomials; fixed columns are indexed by column, not query position. -/
structure PlonkPublicPolynomials (actions : ℕ) where
  instances : Fin actions → CPoly
  fixed : Fin 29 → CPoly
  sigma : Fin 15 → CPoly

/-- The pinned fixed-query order, also used in the suffix of opening group zero.
Array storage avoids repeated evaluation of nested function readers. -/
def plonkFixedQueryOrder : Fin 29 → Fin 29 :=
  (⟨#[3, 0, 11, 4, 5, 6, 7, 8, 9, 10, 12, 1, 2, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28], rfl⟩ : Vector (Fin 29) 29).get

/-- Advice query order; point indices zero, one, two denote `x`, `xω`, `xω⁻¹`. -/
def plonkAdviceQueryOrder : Fin 25 → Fin 10 × Fin 3 :=
  (⟨#[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0),
    (9, 1), (9, 2), (2, 1), (3, 1), (4, 1), (5, 1), (0, 1), (1, 1), (7, 1), (8, 1),
    (6, 2), (1, 2), (6, 1), (7, 2), (8, 2)], rfl⟩ : Vector (Fin 10 × Fin 3) 25).get

/-- Collapse the eight quotient pieces at `x`, retaining a degree-less-than-2048 polynomial. -/
def plonkCollapsedQuotient (x : Fp) (pieces : Fin 8 → CPoly) : CPoly :=
  ∑ j, CPolynomial.C (x ^ (2048 * j.val)) * pieces j

/-- The first group's ordered prefix, ending in `H_x` immediately before the linear mask. -/
def plonkFirstGroupPrefix {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x : Fp) (pieces : Fin 8 → CPoly) : List CPoly :=
  (List.finRange actions).flatMap (fun a =>
    [pub.instances a] ++ (List.finRange 3).map (fun l => privateColumnPolynomial rows (.lookupTable a l))) ++
  (List.finRange 29).map (fun j => pub.fixed (plonkFixedQueryOrder j)) ++
  (List.finRange 15).map pub.sigma ++ [plonkCollapsedQuotient x pieces]

/-- The other four groups contain only these private columns, in Action-major order. -/
def plonkPrivateGroupMembers (actions : ℕ) : Fin 4 → List (PrivateColumnId actions) :=
  ![(List.finRange actions).flatMap (fun a =>
      [.advice a 0, .advice a 2, .advice a 3, .advice a 4, .advice a 5,
       .permutationProduct a 2, .lookupProduct a 0, .lookupProduct a 1, .lookupProduct a 2]),
    (List.finRange actions).flatMap (fun a =>
      [.advice a 1, .advice a 6, .advice a 7, .advice a 8, .advice a 9]),
    (List.finRange actions).flatMap (fun a => [.permutationProduct a 0, .permutationProduct a 1]),
    (List.finRange actions).flatMap (fun a => [.lookupInput a 0, .lookupInput a 1, .lookupInput a 2])]

/-- The exact five polynomial groups, with `r` last in the first group. -/
def plonkOpeningGroups {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) :
    Fin 5 → List CPoly :=
  Fin.cons (plonkFirstGroupPrefix pub rows x pieces ++ [linearMaskPolynomial coefficients])
    (fun i => (plonkPrivateGroupMembers actions i).map (privateColumnPolynomial rows))

/-- The five concrete `Q_i` polynomials from the pinned `x₁` fold. -/
def plonkOpeningPolynomials {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x x1 : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) :
    Fin 5 → CPoly :=
  fun i => plonkPolynomialFold x1 (plonkOpeningGroups pub rows x pieces coefficients i)

/-- The non-mask contribution to `Q₀(q)`, with exactly its Horner weight. -/
def plonkFirstGroupOffset {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x x1 q : Fp) (pieces : Fin 8 → CPoly) : Fp :=
  plonkScalarFold x1 ((plonkFirstGroupPrefix pub rows x pieces).map fun poly => poly.eval q) * x1

/-- No nonzero `x₁` premise is needed: the final linear mask has coefficient one. -/
theorem plonkFirstGroup_eval {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x x1 q : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) :
    (plonkOpeningPolynomials pub rows x x1 pieces coefficients 0).eval q =
      plonkFirstGroupOffset pub rows x x1 q pieces + (linearMaskPolynomial coefficients).eval q := by
  rw [plonkOpeningPolynomials, plonkPolynomialFold_eval]
  simp only [plonkOpeningGroups, Fin.cons_zero, List.map_append, List.map_cons, List.map_nil,
    plonkScalarFold, horner_last_unit_weight, plonkFirstGroupOffset]

/-- The concrete pair `(r(x), Q₀(q))` has exactly the view proved hidden by Common #267. -/
theorem plonkFirstGroup_linearMaskView {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x x1 q : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) :
    ((linearMaskPolynomial coefficients).eval x,
      (plonkOpeningPolynomials pub rows x x1 pieces coefficients 0).eval q) =
      linearMaskView x q (fun _ => plonkFirstGroupOffset pub rows x x1 q pieces) coefficients := by
  rw [plonkFirstGroup_eval]
  simp [linearMaskView, linearMaskPair, addSecondEquiv, linearMaskPolynomial]

/-- Every later group evaluation is an explicit fold of the fifth column observation. -/
def plonkPrivateGroupValues {actions : ℕ} (x1 : Fp) (views : List (Fin 5 → Fp)) : Fin 4 → Fp :=
  fun i => plonkScalarFold x1 ((plonkPrivateGroupMembers actions i).map fun id => privateColumnView views id 4)

/-- Evaluation of groups one through four commutes with the public projection of the trace. -/
theorem plonkPrivateGroupValues_observe {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x x1 q : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp)
    (i : Fin 4) :
    plonkPrivateGroupValues (actions := actions) x1 (observeColumnRows (omegaOf 11)
        (plonkObservationPoints (omegaOf 11) x q) rows) i =
      (plonkOpeningPolynomials pub rows x x1 pieces coefficients i.succ).eval q := by
  rw [plonkOpeningPolynomials, plonkPolynomialFold_eval]
  simp [plonkPrivateGroupValues, plonkOpeningGroups, List.map_map,
    privateColumnView_observe, plonkObservationPoints, Function.comp_def]

end Zcash.Snark.ZeroKnowledge
