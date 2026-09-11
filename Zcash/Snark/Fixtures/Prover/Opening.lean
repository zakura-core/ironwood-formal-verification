import Zcash.Snark.Fixtures.Prover.Division
import Zcash.Snark.Fixtures.Prover.Numerator
import Zcash.Snark.ZeroKnowledge.DenseCollapsedQuotientCost
import Zcash.Snark.ZeroKnowledge.DenseOpeningPolynomialCost
import Zcash.Snark.ZeroKnowledge.DenseQuotientPieces
import Zcash.Snark.ZeroKnowledge.StoredPlonkOpeningGroupsCost
import Zcash.Snark.ZeroKnowledge.StoredMultiopenDataCost

/-!
# Replaying the quotient and multi-opening

The cached numerator feeds iterative division proved equal to the existing dense
algorithm. The eight pieces and their blinds collapse with powers computed by squaring:
the reference power loop recurses once per exponent step, and the largest exponent,
`2048 * 7`, exceeds the interpreter's stack. The five opening groups retain their
original membership, order, point sets, and inherited blinds. No captured output is
used in these computations.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp omegaOf powFast powFast_eq_pow)
open Zcash.Snark Zcash.Snark.ZeroKnowledge CompPoly

/-- Divide the complete numerator by the row-domain polynomial and retain all eight pieces. -/
def quotientPieces {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (columns : List (List Fp)) : List (List Fp) :=
  splitQuotient (numerator vk pub ch columns).val.toList

/-- Stored division yields the reference quotient pieces for the exact cached numerator. -/
theorem quotientPieces_result {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : ColumnHistory 2048) :
    (quotientPieces vk pub ch (columnCoefficients rows)).map densePolynomial =
      List.ofFn (plonkQuotientPieces (plonkConstraintNumerator vk pub ch rows)) := by
  rw [quotientPieces, splitQuotient_result, densePlonkQuotientPiecesCosted_result,
    storedCoefficients_result, numerator_result]

/-- Collapse the eight quotient pieces, computing each power `x ^ (2048 * j)` by squaring. -/
def collapsedQuotient (x : Fp) (pieces : List (List Fp)) : List Fp :=
  (densePolynomialSumCosted 0 0 (List.ofFn fun j : Fin 8 =>
    (denseScaleCosted 0 0 (powFast x (2048 * j.val), 0) (pieces.getD j.val [])).1)).1

/-- The collapse denotes the reference collapsed quotient of the stored pieces. -/
theorem collapsedQuotient_result (x : Fp) (pieces : List (List Fp)) :
    densePolynomial (collapsedQuotient x pieces) =
      plonkCollapsedQuotient x (fun j => densePolynomial (pieces.getD j.val [])) := by
  simp only [collapsedQuotient, densePolynomialSumCosted_result, List.map_ofFn,
    Function.comp_def, denseScaleCosted_result, powFast_eq_pow, List.sum_ofFn,
    plonkCollapsedQuotient]

/-- Prepare the five original opening polynomials with stored public and private coefficients. -/
def openingPolynomials {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (columns pieces : List (List Fp)) (x x1 : Fp) (linear : Fp × Fp) : List (List Fp) :=
  let instances := cacheFn (fun a => ((pub.instances a).val.toList, 0))
  let fixed := cacheFn (fun c => ((pub.fixed c).val.toList, 0))
  let sigma := cacheFn (fun c => ((pub.sigma c).val.toList, 0))
  let quotient := (collapsedQuotient x pieces, 0)
  let mask := denseLinearMaskCosted (linear.1, 0) (linear.2, 0)
  List.ofFn fun group : Fin 5 =>
    (denseOpeningPolynomialCosted 0 0 0 0 instances.get fixed.get sigma.get columns quotient mask (x1, 0) group).1

/-- Dense private coefficient routing agrees with the reference column lookup, including missing slots. -/
theorem privateCoefficients_result {actions : ℕ} (rows : ColumnHistory 2048) (id : PrivateColumnId actions) :
    densePolynomial (privateColumnCoefficientsCosted 0 0 (columnCoefficients rows) id).1 =
      privateColumnPolynomial rows id := by
  rw [privateColumnCoefficientsCosted_result, columnCoefficients_result]
  rfl

/-- The five stored folds denote the actual multi-opening polynomials in their original order. -/
theorem openingPolynomials_result {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (pieces : List (List Fp)) (x x1 : Fp) (linear : Fp × Fp) :
    (openingPolynomials pub (columnCoefficients rows) pieces x x1 linear).map densePolynomial =
      List.ofFn (plonkOpeningPolynomials pub rows x x1
        (fun i : Fin 8 => densePolynomial (pieces.getD i.val [])) linear) := by
  simp only [openingPolynomials, cacheFn_result, List.map_ofFn, Function.comp_def]
  congr 1
  funext group
  apply denseOpeningPolynomialCosted_result
  · exact fun a => storedCoefficients_result (pub.instances a)
  · exact fun c => storedCoefficients_result (pub.fixed c)
  · exact fun c => storedCoefficients_result (pub.sigma c)
  · exact privateCoefficients_result rows
  · exact collapsedQuotient_result x pieces
  · exact denseLinearMaskCosted_result (linear.1, 0) (linear.2, 0)

/-- Collapse the eight quotient-piece blinds with the same squared powers. -/
def collapsedQuotientBlind {actions : ℕ} (x : Fp) (entries : Fin (22 * actions + 10) → Fp × ℕ) :
    Fp × ℕ :=
  sumFinCosted 0 fun piece : Fin 8 =>
    (powFast x (2048 * piece.val) * (plonkPieceEntryCosted entries piece).1, 0)

/-- The squared powers give the reference collapsed quotient blind. -/
theorem collapsedQuotientBlind_result {actions : ℕ} (x : Fp)
    (entries : Fin (22 * actions + 10) → Fp × ℕ) :
    (collapsedQuotientBlind x entries).1 = (collapsedQuotientPointCosted 0 0 0 (x, 0) entries).1 := by
  simp only [collapsedQuotientBlind, collapsedQuotientPointCosted, sumFinCosted_result,
    powFast_eq_pow, fieldPowerCosted_result, smul_eq_mul]

/-- Each group's inherited blinds in the reference order, with the quotient member collapsed by
`collapsedQuotientBlind`. -/
def blindMembers {actions : ℕ} (entries : Fin (22 * actions + 10) → Fp × ℕ) (x : Fp)
    (group : Fin 5) : List Fp :=
  Fin.cases
    (firstOpeningGroupCosted (fun _ : Fin actions => ((1 : Fp), 1))
      (fun action lookup => plonkColumnEntryCosted 0 entries (.lookupTable action lookup))
      (fun _ : Fin 29 => ((1 : Fp), 1)) (fun _ : Fin 15 => ((1 : Fp), 1))
      (collapsedQuotientBlind x entries) (plonkLinearEntryCosted entries)).1
    (fun index => (mapListCosted (plonkColumnEntryCosted 0 entries)
      (privateOpeningGroupCosted actions index).1).1) group

/-- Every group's blind members are the reference members. -/
theorem blindMembers_result {actions : ℕ} (entries : Fin (22 * actions + 10) → Fp × ℕ) (x : Fp)
    (group : Fin 5) :
    blindMembers entries x group = (openingBlindMembersCosted ⟨0, 0, 0, 0⟩ 0 entries (x, 0) group).1 := by
  refine Fin.cases ?_ (fun index => ?_) group
  · simp only [blindMembers, openingBlindMembersCosted, Fin.cases_zero,
      firstOpeningGroupCosted_result, collapsedQuotientBlind_result]
  · simp only [blindMembers, openingBlindMembersCosted, Fin.cases_succ]

/-- Attach the original point sets and the blinds selected by the actual commitment layout. -/
def openingGroups {actions : ℕ} (polynomials : List (List Fp))
    (blinds : Fin (22 * actions + 10) → Fp) (x x1 : Fp) : List StoredOpeningGroup :=
  List.ofFn fun index : Fin 5 =>
    ⟨(getDListCosted 0 [] polynomials index.val).1,
      (openingPointSetCosted ⟨0, 0, 0, 0⟩ (omegaOf 11, 0) (x, 0) index).1,
      (scalarHornerCosted 0 0 0 (x1, 0) (blindMembers (fun i => (blinds i, 0)) x index)).1⟩

/-- The group records are exactly the reference records, including every blind. -/
theorem openingGroups_stored {actions : ℕ} (polynomials : List (List Fp))
    (blinds : Fin (22 * actions + 10) → Fp) (x x1 : Fp) :
    openingGroups polynomials blinds x x1 =
      (storedPlonkOpeningGroupsCosted ⟨0, 0, 0, 0⟩ 0 0 0 polynomials
        (fun i => (blinds i, 0)) (x, 0) (x1, 0)).1 := by
  simp only [openingGroups, storedPlonkOpeningGroupsCosted, ofFnCosted_result,
    storedPlonkOpeningGroupCosted, openingGroupBlindCosted, blindMembers_result]

/-- The stored records preserve every polynomial, point set, and inherited blind. -/
theorem openingGroups_result {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (pieces : List (List Fp)) (x x1 : Fp)
    (linear : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp) :
    (openingGroups (openingPolynomials pub (columnCoefficients rows) pieces x x1 linear)
      blinds x x1).map StoredOpeningGroup.erase =
      plonkBlindedOpeningGroups pub rows x x1
        (fun i : Fin 8 => densePolynomial (pieces.getD i.val [])) linear
        (plonkCommitmentBlindsFromVector blinds) := by
  rw [openingGroups_stored]
  exact storedPlonkOpeningGroupsCosted_result _ _ _ _ _ _ _ _ _ _ _ _
    (openingPolynomials_result pub rows pieces x x1 linear)

/-- The fixed group layout meets the dense multi-opening algorithm's point-capacity premise. -/
theorem openingGroups_points {actions : ℕ} (polynomials : List (List Fp))
    (blinds : Fin (22 * actions + 10) → Fp) (x x1 : Fp)
    (group : StoredOpeningGroup) (hgroup : group ∈ openingGroups polynomials blinds x x1) :
    group.points.length ≤ 4 := by
  rw [openingGroups_stored] at hgroup
  exact (storedPlonkOpeningGroupsCosted_points _ _ _ _ _ _ _ _ group hgroup).2.trans (by decide)

/-- Construct quotient-prime, the final IPA coefficients, their blind, and the claimed value. -/
def openingData (groups : List StoredOpeningGroup) (x2 x4 point quotientBlind : Fp) : StoredMultiopenData :=
  (storedMultiopenDataCosted ⟨0, 0, 0, 0⟩ 0 0 0 (x2, 0) (x4, 0) (point, 0) (quotientBlind, 0) groups).1

end Zcash.Snark.Fixtures.Prover
