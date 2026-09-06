import Zcash.Snark.ZeroKnowledge.PlonkMultiopen
import Zcash.Snark.ZeroKnowledge.PlonkTranscript

/-!
# The actual pre-IPA commitment cores

The joint mask theorem allowed arbitrary polynomial commitment cores independent of the
commitment blinds. Here those cores are instantiated by the private row polynomials,
the linear mask, the eight quotient pieces, and the computed multi-opening quotient.
The shared positions are `r`, `h₀,…,h₇`, and `Q'`, in that order.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open CompPoly

/-- The coefficient polynomials of all emitted pre-IPA commitments in their exact order. -/
def plonkCommitmentPolynomials {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (x x1 x2 : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) : Fin (22 * actions + 10) → CPoly :=
  Fin.append (fun i => privateColumnPolynomial rows (privateColumnAt i))
    (Fin.cons (linearMaskPolynomial coefficients)
      (Fin.append (pieces rows) (fun _ : Fin 1 =>
        multiopenQuotientPolynomial x2 (plonkPolynomialOpeningGroups pub rows x x1 (pieces rows) coefficients))))

/-- Read a private column's entry from any pre-IPA point or blind vector. -/
def plonkColumnEntry {actions : ℕ} {A : Type*} (entries : Fin (22 * actions + 10) → A)
    (id : PrivateColumnId actions) : A :=
  entries (Fin.castAdd 10 (privateColumnIndex id))

/-- Read the entry of the linear-mask commitment. -/
def plonkLinearEntry {actions : ℕ} {A : Type*} (entries : Fin (22 * actions + 10) → A) : A :=
  entries (Fin.natAdd (22 * actions) 0)

/-- Read one of the eight quotient-piece entries. -/
def plonkPieceEntry {actions : ℕ} {A : Type*} (entries : Fin (22 * actions + 10) → A)
    (j : Fin 8) : A :=
  entries (Fin.natAdd (22 * actions) (Fin.castAdd 1 j).succ)

/-- The last pre-IPA commitment entry is the computed `Q'`. -/
def plonkQuotientPrimeEntry {actions : ℕ} {A : Type*} (entries : Fin (22 * actions + 10) → A) : A :=
  entries (Fin.natAdd (22 * actions) (9 : Fin 10))

/-- The private-column slot contains precisely that column's polynomial. -/
theorem plonkCommitmentPolynomials_column {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (x x1 x2 : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) (id : PrivateColumnId actions) :
    plonkColumnEntry (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients) id =
      privateColumnPolynomial rows id := by
  simp [plonkColumnEntry, plonkCommitmentPolynomials, privateColumnAt_index]

/-- The linear-mask slot contains the actual two-coefficient polynomial. -/
theorem plonkCommitmentPolynomials_linear {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (x x1 x2 : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) :
    plonkLinearEntry (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients) =
      linearMaskPolynomial coefficients := by
  simp [plonkLinearEntry, plonkCommitmentPolynomials]

/-- The quotient-piece slots retain their supplied order. -/
theorem plonkCommitmentPolynomials_piece {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (x x1 x2 : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) (j : Fin 8) :
    plonkPieceEntry (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients) j = pieces rows j := by
  simp [plonkPieceEntry, plonkCommitmentPolynomials]

/-- The last slot contains the quotient computed without consulting any commitment blind. -/
theorem plonkCommitmentPolynomials_quotientPrime {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (x x1 x2 : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) :
    plonkQuotientPrimeEntry (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients) =
      multiopenQuotientPolynomial x2 (plonkPolynomialOpeningGroups pub rows x x1 (pieces rows) coefficients) := by
  unfold plonkQuotientPrimeEntry plonkCommitmentPolynomials
  rw [Fin.append_right]
  change (Fin.cons _ _) ((Fin.natAdd 8 (0 : Fin 1)).succ) = _
  rw [Fin.cons_succ, Fin.append_right]

/-- Read the inherited blind of every polynomial from the same emitted commitment positions. -/
def plonkCommitmentBlindsFromVector {actions : ℕ} (blinds : Fin (22 * actions + 10) → Fp) :
    PlonkCommitmentBlinds actions where
  columns := plonkColumnEntry blinds
  linear := plonkLinearEntry blinds
  pieces := plonkPieceEntry blinds
  quotientPrime := plonkQuotientPrimeEntry blinds

section Commitments

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The commitment cores depend on rows and linear coefficients, never on the independent blinds. -/
def plonkCommitmentCores {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) : Fin (22 * actions + 10) → G :=
  fun i => commitGen urs.g
    (polynomialCoefficients (2 ^ urs.k) (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients i))

/-- Instantiating the mask view with the actual polynomial commitments and first-group offset. -/
def honestPlonkMaskView {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 q : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp) :
    PreIpaMaskView 5 (22 * actions + 10) G :=
  honestPreIpaMaskView urs.w (omegaOf 11) x q (plonkObservationPoints (omegaOf 11) x q)
    (plonkCommitmentCores urs pub x x1 x2 pieces)
    (fun rows _ => plonkFirstGroupOffset pub rows x x1 q (pieces rows)) rows coefficients blinds

/-- Every emitted point is the coefficient commitment with the blind at that same position. -/
theorem honestPlonkMaskView_points {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 q : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (rows : ColumnHistory 2048) (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp)
    (i : Fin (22 * actions + 10)) :
    (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds).1 i =
      polynomialCommitment urs.g urs.w (plonkCommitmentPolynomials pub x x1 x2 pieces rows coefficients i)
        (blinds i) := rfl

/-- The scalar trace is the common five evaluations of every actual private row polynomial. -/
theorem honestPlonkMaskView_columns {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (rows : ColumnHistory 2048)
    (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp) :
    (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds).2.1 =
      observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x q) rows := rfl

/-- The group values in the public projection are evaluations of the actual opening polynomials. -/
theorem honestPlonkMaskView_groupValues {actions : ℕ} (urs : URS G)
    (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (rows : ColumnHistory 2048)
    (coefficients : Fp × Fp) (blinds : Fin (22 * actions + 10) → Fp) :
    (plonkPreIpaProjection pub x x1
        (honestPlonkMaskView urs pub x x1 x2 q pieces rows coefficients blinds)).groupValues =
      fun i => (plonkOpeningPolynomials pub rows x x1 (pieces rows) coefficients i).eval q := by
  exact (congrArg PlonkPreIpaTranscript.groupValues
    (honestPlonkPreIpaTranscript_projection pub x x1 q urs.w pieces
      (plonkCommitmentCores urs pub x x1 x2 pieces) rows coefficients blinds)).symm

end Commitments

end Zcash.Snark.ZeroKnowledge
