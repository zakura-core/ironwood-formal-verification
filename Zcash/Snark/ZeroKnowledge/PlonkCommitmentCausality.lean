import Zcash.Snark.ZeroKnowledge.PlonkTapeCausality
import Zcash.Snark.ZeroKnowledge.PlonkStageCausality

/-!
# Causality of the emitted private-column commitments

The proof fields are connected to the coefficient commitments formed from the
actual complete prover tape. Advice commitments ignore all challenges; lookup
permutation commitments use only theta; product commitments use only theta,
beta, and gamma. The linear mask ignores every challenge; quotient commitments
add only y. Together these facts give the complete message prefix before x.
These are deterministic equalities, including exceptional values and the
reference constructor's totalized fallbacks.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open CompPoly

/-- Read a private-column commitment directly from its existing verifier-proof field. -/
def plonkProofColumnPoint {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) F G) : PrivateColumnId actions → G
  | .advice a c => proof.adviceCommitments a c
  | .lookupInput a l => proof.lookupPermutedInput a l
  | .lookupTable a l => proof.lookupPermutedTable a l
  | .permutationProduct a s => proof.permutationProduct a s
  | .lookupProduct a l => proof.lookupProduct a l

/-- Every private-column point in the existing proof comes from its specified commitment slot. -/
theorem plonkProofFromJointView_columnPoint {actions k : ℕ} {G : Type*}
    (pub : PlonkPublicPolynomials actions) (x x1 : Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (id : PrivateColumnId actions) :
    plonkProofColumnPoint (plonkProofFromJointView pub x x1 view) id =
      plonkColumnEntry view.1.1 id := by
  cases id <;> rfl

section Commitments

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A material's private-column slot is the commitment to that column with its own decoded blind. -/
theorem plonkMaskViewFromMaterial_column {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions)
    (id : PrivateColumnId actions) :
    plonkColumnEntry (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1 id =
      polynomialCommitment urs.g urs.w (privateColumnPolynomial material.1 id)
        (plonkColumnEntry material.2.2 id) := by
  have h := honestPlonkMaskView_points urs pub x x1 x2 q pieces material.1 material.2.1 material.2.2
    (Fin.castAdd 10 (privateColumnIndex id))
  change plonkColumnEntry (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1 id =
    polynomialCommitment urs.g urs.w
      (plonkColumnEntry (plonkCommitmentPolynomials pub x x1 x2 pieces material.1 material.2.1) id)
      (plonkColumnEntry material.2.2 id) at h
  rwa [plonkCommitmentPolynomials_column] at h

/-- A column commitment ignores later rows, later challenge parameters, and the quotient callback. -/
theorem plonkMaskViewFromMaterial_column_congr {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 q x' x1' x2' q' : Fp)
    (pieces pieces' : ColumnHistory 2048 → Fin 8 → CPoly)
    (left right : PlonkPrivateMaterial actions) (cut : ℕ) (id : PrivateColumnId actions)
    (hindex : (privateColumnIndex id).val < cut)
    (hrows : left.1.take cut = right.1.take cut) (hblinds : left.2.2 = right.2.2) :
    plonkColumnEntry (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces left).1 id =
      plonkColumnEntry (plonkMaskViewFromMaterial urs pub x' x1' x2' q' pieces' right).1 id := by
  rw [plonkMaskViewFromMaterial_column, plonkMaskViewFromMaterial_column]
  rw [← privateColumnPolynomial_take left.1 id cut hindex,
    ← privateColumnPolynomial_take right.1 id cut hindex, hrows, hblinds]

/-- The actual full-tape proof inherits column-prefix causality, including every decoded blind. -/
theorem plonkVerifierProofFromTape_column_prefix {actions : ℕ}
    (construct construct' : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount construct urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount construct' urs.k) → Fp)
    (cut : ℕ) (id : PrivateColumnId actions) (hindex : (privateColumnIndex id).val < cut)
    (hsteps : (plonkColumnSteps construct).take cut = (plonkColumnSteps construct').take cut)
    (htape : TapeAgrees tape tape') :
    plonkProofColumnPoint (plonkVerifierProofFromTape construct history urs vk pub left tape) id =
      plonkProofColumnPoint (plonkVerifierProofFromTape construct' history urs vk pub right tape') id := by
  have hrows := plonkJointMaterialFromTape_rows_take cut construct construct' history tape tape' hsteps htape
  have hcoins := plonkJointMaterialFromTape_coins_congr construct construct' history history tape tape' htape
  unfold plonkVerifierProofFromTape
  rw [plonkProofFromJointView_columnPoint, plonkProofFromJointView_columnPoint]
  exact plonkMaskViewFromMaterial_column_congr urs pub
    left.x left.x1 left.x2 left.x3 right.x right.x1 right.x2 right.x3
    (plonkHonestQuotientPieces vk pub left) (plonkHonestQuotientPieces vk pub right)
    (plonkJointMaterialFromTape construct history tape) (plonkJointMaterialFromTape construct' history tape')
    cut id hindex hrows (congrArg Prod.snd hcoins)

/-- The first emitted advice commitments are fixed before every verifier challenge. -/
theorem plonkVerifierProofFromTape_advice_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).adviceCommitments =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').adviceCommitments := by
  funext a c
  exact plonkVerifierProofFromTape_column_prefix _ _ [] urs vk pub left right tape tape'
    (10 * actions) (.advice a c) (privateColumnIndex_bounds (.advice a c))
    (plonkColumnSteps_take_before_theta vk pub witness left right) htape

/-- Both emitted lookup-permutation commitment vectors depend only on the earlier `theta`. -/
theorem plonkVerifierProofFromTape_lookup_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htheta : left.theta = right.theta) (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).lookupPermutedInput =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').lookupPermutedInput ∧
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).lookupPermutedTable =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').lookupPermutedTable := by
  have hpoint (id : PrivateColumnId actions) (hindex : (privateColumnIndex id).val < 16 * actions) :=
    plonkVerifierProofFromTape_column_prefix _ _ [] urs vk pub left right tape tape'
      (16 * actions) id hindex (plonkColumnSteps_take_challenges vk pub witness left right htheta) htape
  constructor
  · funext a l
    exact hpoint (.lookupInput a l) (privateColumnIndex_bounds (.lookupInput a l)).2
  · funext a l
    exact hpoint (.lookupTable a l) (privateColumnIndex_bounds (.lookupTable a l)).2

/-- Both product-commitment vectors use no challenges after `theta,beta,gamma`. -/
theorem plonkVerifierProofFromTape_products_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).permutationProduct =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').permutationProduct ∧
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).lookupProduct =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').lookupProduct := by
  have hsteps :
      (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness left)).take (22 * actions) =
        (plonkColumnSteps (plonkTotalColumnConstructor vk pub witness right)).take (22 * actions) := by
    rw [plonkTotalColumnConstructor_challenges vk pub witness left right htheta hbeta hgamma]
  have hpoint (id : PrivateColumnId actions) :=
    plonkVerifierProofFromTape_column_prefix _ _ [] urs vk pub left right tape tape'
      (22 * actions) id (privateColumnIndex id).isLt hsteps htape
  constructor
  · funext a s
    exact hpoint (.permutationProduct a s)
  · funext a l
    exact hpoint (.lookupProduct a l)

/-- The linear-mask commitment uses only its two coefficients and its decoded blind. -/
theorem plonkMaskViewFromMaterial_linear {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions) :
    plonkLinearEntry (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1 =
      polynomialCommitment urs.g urs.w (linearMaskPolynomial material.2.1)
        (plonkLinearEntry material.2.2) := by
  have h := honestPlonkMaskView_points urs pub x x1 x2 q pieces material.1 material.2.1 material.2.2
    (Fin.natAdd (22 * actions) 0)
  change plonkLinearEntry (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1 =
    polynomialCommitment urs.g urs.w
      (plonkLinearEntry (plonkCommitmentPolynomials pub x x1 x2 pieces material.1 material.2.1))
      (plonkLinearEntry material.2.2) at h
  rwa [plonkCommitmentPolynomials_linear] at h

/-- A quotient-piece commitment uses the computed piece and its decoded blind. -/
theorem plonkMaskViewFromMaterial_piece {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions) (j : Fin 8) :
    plonkPieceEntry (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1 j =
      polynomialCommitment urs.g urs.w (pieces material.1 j) (plonkPieceEntry material.2.2 j) := by
  have h := honestPlonkMaskView_points urs pub x x1 x2 q pieces material.1 material.2.1 material.2.2
    (Fin.natAdd (22 * actions) (Fin.castAdd 1 j).succ)
  change plonkPieceEntry (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1 j =
    polynomialCommitment urs.g urs.w
      (plonkPieceEntry (plonkCommitmentPolynomials pub x x1 x2 pieces material.1 material.2.1) j)
      (plonkPieceEntry material.2.2 j) at h
  rwa [plonkCommitmentPolynomials_piece] at h

/-- The actual emitted linear-mask commitment is independent of the entire verifier tape. -/
theorem plonkVerifierProofFromTape_linear_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).vanishingRandom =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').vanishingRandom := by
  have hcoins := plonkJointMaterialFromTape_coins_congr
    (plonkTotalColumnConstructor vk pub witness left) (plonkTotalColumnConstructor vk pub witness right)
    [] [] tape tape' htape
  change plonkLinearEntry (plonkMaskViewFromMaterial urs pub left.x left.x1 left.x2 left.x3
      (plonkHonestQuotientPieces vk pub left)
      (plonkJointMaterialFromTape _ [] tape)).1 =
    plonkLinearEntry (plonkMaskViewFromMaterial urs pub right.x right.x1 right.x2 right.x3
      (plonkHonestQuotientPieces vk pub right)
      (plonkJointMaterialFromTape _ [] tape')).1
  rw [plonkMaskViewFromMaterial_linear, plonkMaskViewFromMaterial_linear, hcoins]

/-- All eight quotient commitments are fixed before the evaluation challenge `x`. -/
theorem plonkVerifierProofFromTape_quotient_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (hy : left.y = right.y) (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).hPieces =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').hPieces := by
  have hmaterial := plonkJointMaterialFromTape_congr _ _ [] tape tape'
    (plonkTotalColumnConstructor_challenges vk pub witness left right htheta hbeta hgamma) htape
  have hpieces : plonkHonestQuotientPieces vk pub left = plonkHonestQuotientPieces vk pub right :=
    funext fun rows => plonkHonestQuotientPieces_challenges vk pub left right rows htheta hbeta hgamma hy
  funext j
  change plonkPieceEntry (plonkMaskViewFromMaterial urs pub left.x left.x1 left.x2 left.x3
      (plonkHonestQuotientPieces vk pub left) (plonkJointMaterialFromTape _ [] tape)).1 j =
    plonkPieceEntry (plonkMaskViewFromMaterial urs pub right.x right.x1 right.x2 right.x3
      (plonkHonestQuotientPieces vk pub right) (plonkJointMaterialFromTape _ [] tape')).1 j
  rw [plonkMaskViewFromMaterial_piece, plonkMaskViewFromMaterial_piece, hmaterial, hpieces]

/-- The actual whole message prefix before `x` depends only on the four challenges already received. -/
theorem plonkAttemptTrace_prefix_before_x {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (hy : left.y = right.y) (htape : TapeAgrees tape tape') :
    protocolPrefix 4 (plonkAttemptTrace
        (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left tape)) =
      protocolPrefix 4 (plonkAttemptTrace
        (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right tape')) := by
  let lproof := plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left tape
  let rproof := plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right tape'
  have hadvice := plonkVerifierProofFromTape_advice_causal urs vk pub witness left right tape tape' htape
  have hlookup := plonkVerifierProofFromTape_lookup_causal urs vk pub witness left right tape tape' htheta htape
  have hproducts := plonkVerifierProofFromTape_products_causal urs vk pub witness left right tape tape'
    htheta hbeta hgamma htape
  have hlinear := plonkVerifierProofFromTape_linear_causal urs vk pub witness left right tape tape' htape
  have hquotient := plonkVerifierProofFromTape_quotient_causal urs vk pub witness left right tape tape'
    htheta hbeta hgamma hy htape
  have hpre (i : Fin 11) (hi : i.val ≤ 4) : plonkPreIpaStages lproof i = plonkPreIpaStages rproof i := by
    fin_cases i <;> simp_all [plonkPreIpaStages, lproof, rproof]
  rw [plonkAttemptTrace_eq_stages, plonkAttemptTrace_eq_stages]
  apply protocolStagesTrace_prefix_congr
  · exact plonkStageMessages_challengeCount lproof
  · exact plonkStageMessages_challengeCount rproof
  · intro j hj
    let i : Fin 11 := ⟨j.val, by omega⟩
    have heq : j = Fin.castAdd urs.k i := Fin.ext rfl
    rw [heq]
    calc
      _ = plonkPreIpaStages lproof i := by unfold plonkStageMessages; exact Fin.addCases_left i
      _ = plonkPreIpaStages rproof i := hpre i hj
      _ = _ := by symm; unfold plonkStageMessages; exact Fin.addCases_left i
  · intro h
    omega

end Commitments

end Zcash.Snark.ZeroKnowledge
