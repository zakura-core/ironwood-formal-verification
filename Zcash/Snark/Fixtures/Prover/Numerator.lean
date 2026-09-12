import Zcash.Snark.Fixtures.Prover.Polynomial
import Zcash.Snark.ZeroKnowledge.PlonkConstraints

/-!
# Replaying the honest constraint numerator

Cached row interpolants and coefficient rotations feed the existing polynomial
claim layout. The existing ring-generic constraint builder runs with an explicit,
proved-equal NTT multiplication dictionary. Its result is the reference prover's
numerator for the same private rows, including exceptional field values.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Snark Zcash.Snark.ZeroKnowledge CompPoly

/-- Store every row interpolant once before it is used by several queries. -/
def columnCoefficients (rows : List (Fin 2048 → Fp)) : List (List Fp) :=
  rows.map (rowCoefficients 11 (by decide))

/-- The stored coefficients denote exactly the reference private-column polynomials. -/
theorem columnCoefficients_result (rows : List (Fin 2048 → Fp)) :
    (columnCoefficients rows).map densePolynomial = rows.map (rowPolynomial (omegaOf 11)) := by
  simp only [columnCoefficients, List.map_map, Function.comp_def, rowCoefficients_result]
  rfl

/-- Rotate a coefficient vector using the existing linear running-power algorithm. -/
def rotateCoefficients (coefficients : List Fp) (factor : Fp) : CPoly :=
  CPolynomial.ofArray (denseRotateCosted 0 0 (factor, 0) coefficients).1.toArray

/-- The array rotation is precisely composition by the linear variable substitution. -/
theorem rotateCoefficients_result (coefficients : List Fp) (factor : Fp) :
    rotateCoefficients coefficients factor =
      (densePolynomial coefficients).comp (CPolynomial.C factor * CPolynomial.X) := by
  rw [rotateCoefficients, ← densePolynomial_ofArray, denseRotateCosted_result]

/-- Cache all four rotations before the constraint expressions repeatedly query them. -/
def rotatedColumns (coefficients : List (List Fp)) : List (Vector CPoly 4) :=
  coefficients.map fun values =>
    cacheFn (fun i : Fin 4 => rotateCoefficients values (plonkQueryFactors i))

/-- Route a query through the materialized rotation vectors, retaining the zero default. -/
def readRotated {actions : ℕ} (prepared : List (Vector CPoly 4))
    (id : PrivateColumnId actions) (i : Fin 4) : CPoly :=
  (prepared.getD ((privateColumnOrder actions).idxOf id) (cacheFn (fun _ => 0))).get i

/-- A missing coefficient vector and every materialized rotation have the model's zero default. -/
theorem rotatedColumns_result {actions : ℕ} (rows : List (Fin 2048 → Fp))
    (id : PrivateColumnId actions) (i : Fin 4) :
    readRotated (rotatedColumns (columnCoefficients rows)) id i = plonkRotatedColumn rows id i := by
  have hzero (factor : Fp) : rotateCoefficients [] factor = 0 := by
    rw [rotateCoefficients_result, densePolynomial]
    apply CPolynomial.toPoly_injective
    simp only [CPolynomial.toPoly_comp, CPolynomial.toPoly_zero, Polynomial.zero_comp]
  have hdefault : cacheFn (fun i : Fin 4 => rotateCoefficients [] (plonkQueryFactors i)) =
      cacheFn (fun _ : Fin 4 => 0) := by
    congr 1
    funext i
    exact hzero _
  unfold readRotated rotatedColumns
  rw [← hdefault, List.getD_map]
  simp only [cacheFn_result, rotateCoefficients_result]
  have h := List.getD_map (l := columnCoefficients rows) (d := [])
    (n := (privateColumnOrder actions).idxOf id) densePolynomial
  rw [densePolynomial, columnCoefficients_result] at h
  rw [← h]
  rfl

/-- Cache all public interpolants without evaluating a row interpolation anew at each query. -/
def publicPolynomials {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) :
    PlonkPublicPolynomials actions :=
  let instancePolys := cacheFn (fun a => interpolateRows 11 (by decide) (instances a))
  let fixedPolys := cacheFn (fun c => interpolateRows 11 (by decide) (fixed c))
  let sigmaPolys := cacheFn (fun c => interpolateRows 11 (by decide) (sigma c))
  ⟨instancePolys.get, fixedPolys.get, sigmaPolys.get⟩

/-- Public caching supplies the original canonical instance, fixed, and sigma polynomials. -/
theorem publicPolynomials_result {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp) :
    publicPolynomials instances fixed sigma = plonkPublicPolynomialsFromRows instances fixed sigma := by
  simp only [publicPolynomials, cacheFn_result, interpolateRows_result, plonkPublicPolynomialsFromRows]

/-- The three canonical selector row vectors are interpolated with the same checked transform. -/
def selectors : CPoly × CPoly × CPoly :=
  (interpolateRows 11 (by decide) (Pi.single 0 1),
    interpolateRows 11 (by decide) (Pi.single (lastUsableDomainRow (by decide : 5 < 2048)) 1),
    interpolateRows 11 (by decide) (fun row : Fin 2048 => if 2042 < row.val then 1 else 0))

/-- The cached selectors are the exact triple appearing in the reference numerator. -/
theorem selectors_result : selectors = plonkSelectors := by
  unfold selectors plonkSelectors canonicalLagrangePolynomials rowSelectorPolynomial blindSelectorPolynomial
  simp only [interpolateRows_result]
  rfl

/-- Route cached claims through the reference query layout and constraint metadata. -/
def constraintModel {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (column : PrivateColumnId actions → Fin 4 → CPoly) :
    ConstraintPolyModel actions :=
  let ps : ProofString (plonkProofShape actions k) CPoly G :=
    plonkClaimProof pub.instances pub.fixed pub.sigma column
  { fixedCols := finFn ps.fixedEvals
    adviceCols := fun a => finFn (ps.adviceEvals a)
    instanceCols := fun a => finFn (ps.instanceEvals a)
    gates := vk.gates
    sets := fun a => List.ofFn (ps.permutationSetEvals a)
    chunks := fun a => ((List.ofFn (ps.permutationSetEvals a)).zip vk.permutationChunks).map fun sc =>
      (sc.1, sc.2.map fun cr =>
        (cr.1.resolve (finFn (ps.instanceEvals a)) (finFn (ps.adviceEvals a)) (finFn ps.fixedEvals),
          finFn ps.permutationCommonEvals cr.2))
    lookups := fun a => List.ofFn fun l => (ps.lookupEvals a l, vk.lookupInputExprs l, vk.lookupTableExprs l)
    beta := ch.beta
    gamma := ch.gamma
    delta := vk.delta
    theta := ch.theta
    chunkLen := vk.chunkLen
    l0 := selectors.1
    lLast := selectors.2.1
    lBlind := selectors.2.2 }

/-- With the proved row claims, routing yields the complete original polynomial constraint model. -/
theorem constraintModel_result {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : List (Fin 2048 → Fp)) :
    constraintModel vk pub ch (readRotated (rotatedColumns (columnCoefficients rows))) =
      plonkConstraintModel vk pub ch rows := by
  have hcolumn : readRotated (actions := actions) (rotatedColumns (columnCoefficients rows)) =
      plonkRotatedColumn rows := funext fun id => funext (rotatedColumns_result rows id)
  rw [hcolumn]
  unfold constraintModel
  rw [selectors_result]
  rfl

/-- Evaluate the existing constraint program with the explicitly supplied multiplication dictionary. -/
def numeratorFromModel {actions : ℕ} (model : ConstraintPolyModel actions) (y : Fp) : CPoly :=
  let constraints := @allConstraints CPoly polynomialRing actions
    model.fixedCols model.adviceCols model.instanceCols (model.gates.map (Expr.map CPolynomial.C))
    model.sets model.chunks
    (fun a => (model.lookups a).map fun lk =>
      (lk.1, lk.2.1.map (Expr.map CPolynomial.C), lk.2.2.map (Expr.map CPolynomial.C)))
    (CPolynomial.C model.beta) (CPolynomial.C model.gamma) CPolynomial.X
    (CPolynomial.C model.delta) (CPolynomial.C model.theta) model.chunkLen
    model.l0 model.lLast model.lBlind
  constraints.foldl (fun acc value => multiply acc (CPolynomial.C y) + value) 0

/-- Dictionary replacement preserves the full constraint list and its Horner order. -/
theorem numeratorFromModel_result {actions : ℕ} (model : ConstraintPolyModel actions) (y : Fp) :
    numeratorFromModel model y =
      combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
        model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta y
        model.chunkLen model.l0 model.lLast model.lBlind := by
  unfold numeratorFromModel
  rw [polynomialRing_result]
  simp only [multiply_result]
  rfl

/-- Construct the numerator from cached row polynomials and the actual received challenges. -/
def numerator {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (coefficients : List (List Fp)) : CPoly :=
  let prepared := rotatedColumns coefficients
  numeratorFromModel (constraintModel vk pub ch (readRotated prepared)) ch.y

/-- The entire executable numerator agrees with the reference prover for every supplied row state. -/
theorem numerator_result {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (rows : List (Fin 2048 → Fp)) :
    numerator vk pub ch (columnCoefficients rows) = plonkConstraintNumerator vk pub ch rows := by
  rw [numerator, constraintModel_result, numeratorFromModel_result]
  rfl

end Zcash.Snark.Fixtures.Prover
