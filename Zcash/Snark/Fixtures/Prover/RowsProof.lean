import Zcash.Snark.Fixtures.Prover.ProofCore
import Zcash.Snark.ZeroKnowledge.CommitmentCoefficientRoutingCost
import Zcash.Snark.ZeroKnowledge.PlonkProofString
import Zcash.Snark.ZeroKnowledge.PlonkComposition

/-!
# Assembling every prover message from stored private rows

The common proof constructor fixes the query and commitment order. The executable
inputs are private rows, quotient pieces, masks, blinds, and the IPA tape; no
captured commitment or scalar response is an input.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp omegaOf URS)
open Zcash.Snark Zcash.Snark.ZeroKnowledge CompPoly

/-- Reading a stored polynomial commutes with its denotation, including missing entries. -/
theorem polynomial_getD (polynomials : List (List Fp)) (i : ℕ) :
    densePolynomial (polynomials.getD i []) = (polynomials.map densePolynomial).getD i 0 := by
  simpa only [densePolynomial] using
    (List.getD_map (l := polynomials) (n := i) (d := []) densePolynomial).symm

/-- Evaluate a coefficient list with the existing dense Horner loop. -/
def evaluate (coefficients : List Fp) (point : Fp) : Fp :=
  (listHornerCosted 0 0 0 (point, 0) coefficients).1

/-- Horner evaluation returns the reference polynomial's value. -/
theorem evaluate_result (coefficients : List Fp) (point : Fp) :
    evaluate coefficients point = (densePolynomial coefficients).eval point :=
  listHornerCosted_densePolynomial_result 0 0 0 (point, 0) coefficients

/-- Materialize all pre-IPA commitments in their original private and shared slots. -/
def commitmentPoints {actions : ℕ} (urs : URS VestaG) (columns pieces : List (List Fp))
    (linear : Fp × Fp) (data : StoredMultiopenData) (blinds : Fin (22 * actions + 10) → Fp) :
    Vector VestaG (22 * actions + 10) :=
  let mask := denseLinearMaskCosted (linear.1, 0) (linear.2, 0)
  cacheFn (fun i => commitPolynomial urs.g urs.w
    (plonkCommitmentCoefficientCosted 0 0 columns pieces mask (data.quotientPrime, 0) i).1 (blinds i))

/-- Every stored point is the reference commitment to the corresponding constructed polynomial. -/
theorem commitmentPoints_result {actions : ℕ} (urs : URS VestaG)
    (pub : PlonkPublicPolynomials actions) (ch : Challenges urs.k Fp)
    (rows : ColumnHistory 2048) (pieces : List (List Fp)) (linear : Fp × Fp)
    (blinds : Fin (22 * actions + 10) → Fp) (i : Fin (22 * actions + 10)) :
    (commitmentPoints urs (columnCoefficients rows) pieces linear
      (openingData (openingGroups (openingPolynomials pub (columnCoefficients rows) pieces ch.x ch.x1 linear)
        blinds ch.x ch.x1) ch.x2 ch.x4 ch.x3 (plonkQuotientPrimeEntry blinds)) blinds).get i =
      (honestPlonkMaskView urs pub ch.x ch.x1 ch.x2 ch.x3
        (fun _ j => densePolynomial (pieces.getD j.val [])) rows linear blinds).1 i := by
  rw [commitmentPoints, cacheFn_result, commitPolynomial_result,
    plonkCommitmentCoefficientCosted_result, columnCoefficients_result,
    denseLinearMaskCosted_result, openingData,
    storedMultiopenDataCosted_quotient_result _ _ _ _ _ _ _ _ _
      (openingGroups_points _ blinds ch.x ch.x1)]
  rw [show (openingGroups (openingPolynomials pub (columnCoefficients rows) pieces ch.x ch.x1 linear)
        blinds ch.x ch.x1).map (fun g => g.erase.toPolynomialOpeningGroup) =
      ((openingGroups (openingPolynomials pub (columnCoefficients rows) pieces ch.x ch.x1 linear)
        blinds ch.x ch.x1).map StoredOpeningGroup.erase).map
          BlindedOpeningGroup.toPolynomialOpeningGroup by rw [List.map_map]; rfl,
    openingGroups_result, plonkBlindedOpeningGroups_polynomials, honestPlonkMaskView_points]
  rfl

/-- Assemble the entire proof, including all multi-opening and IPA messages. -/
def proofFromRows {actions : ℕ} (urs : URS VestaG) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (rows : ColumnHistory 2048) (pieces : List (List Fp))
    (linear : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp)
    (ipaTape : Fin (ipaSampleCount urs.k) → Fp) : ProofString (plonkProofShape actions urs.k) Fp VestaG :=
  let columns := columnCoefficients rows
  let polynomials := openingPolynomials pub columns pieces ch.x ch.x1 linear
  let groups := openingGroups polynomials blinds ch.x ch.x1
  let data := openingData groups ch.x2 ch.x4 ch.x3 (plonkQuotientPrimeEntry blinds)
  let points := commitmentPoints urs columns pieces linear data blinds
  let tail := storedIpa urs data ch.x3 ch.xi ch.z ch.ipaRound ipaTape
  let instances := cacheFn (fun a => evaluate (pub.instances a).val.toList ch.x)
  let fixed := cacheFn (fun c => evaluate (pub.fixed c).val.toList ch.x)
  let sigma := cacheFn (fun c => evaluate (pub.sigma c).val.toList ch.x)
  let values := cacheFn (fun i : Fin 5 => evaluate (polynomials.getD i.val []) ch.x3)
  plonkProofString instances.get fixed.get sigma.get
    (fun id i => evaluate (privateColumnCoefficientsCosted 0 0 columns id).1
      (plonkObservationPoints (omegaOf 11) ch.x ch.x3 i.castSucc))
    points.get (linear.1 + linear.2 * ch.x) values.get tail

/-- The assembled fields are exactly the reference joint view on the same private rows and coins. -/
theorem proofFromRows_result {actions : ℕ} (urs : URS VestaG)
    (pub : PlonkPublicPolynomials actions) (ch : Challenges urs.k Fp)
    (rows : ColumnHistory 2048) (pieces : List (List Fp)) (linear : Fp × Fp)
    (blinds : Fin (22 * actions + 10) → Fp) (ipaTape : Fin (ipaSampleCount urs.k) → Fp) :
    proofFromRows urs pub ch rows pieces linear blinds ipaTape =
      let piecePolys := fun _ : ColumnHistory 2048 => fun j : Fin 8 => densePolynomial (pieces.getD j.val [])
      let data := plonkIpaData urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z ch.ipaRound
        piecePolys (rows, linear, blinds)
      plonkProofFromJointView pub ch.x ch.x1
        (honestPlonkMaskView urs pub ch.x ch.x1 ch.x2 ch.x3 piecePolys rows linear blinds,
          ipaTranscriptFromTape data.1 data.2.1 data.2.2 ipaTape) := by
  have hg (i : Fin 5) :
      evaluate ((openingPolynomials pub (columnCoefficients rows) pieces ch.x ch.x1 linear).getD i.val []) ch.x3 =
        (plonkOpeningPolynomials pub rows ch.x ch.x1
          (fun j : Fin 8 => densePolynomial (pieces.getD j.val [])) linear i).eval ch.x3 := by
    rw [evaluate_result, polynomial_getD, openingPolynomials_result,
      List.getD_eq_getElem _ 0 (by simp)]
    simp only [List.getElem_ofFn]
  simp only [proofFromRows, cacheFn_result, evaluate_result, storedCoefficients_result,
    privateCoefficients_result,
    storedIpa_result _ _ _ _ _ _ _ _ _ _ (openingGroups_points _ blinds ch.x ch.x1),
    openingGroups_result, plonkIpaData, plonkProofFromJointView,
    honestPlonkMaskView_columns, privateColumnView_observe, honestPlonkMaskView_groupValues]
  congr 2
  · funext i
    exact commitmentPoints_result urs pub ch rows pieces linear blinds i
  · funext i
    simpa only [evaluate_result] using hg i

end Zcash.Snark.Fixtures.Prover
