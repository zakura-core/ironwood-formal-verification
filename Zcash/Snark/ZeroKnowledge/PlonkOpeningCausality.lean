import Zcash.Snark.ZeroKnowledge.PlonkCommitmentCausality

/-!
# Causality of evaluations and multi-opening messages

The evaluation block uses only the first four column observations and r(x).
The later observation point, commitment fields, and IPA suffix do not enter it.
The Q' commitment precedes its opening point, and the group evaluations precede
the final folding challenge. Every result uses the actual complete prover tape.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open CompPoly

/-- The existing evaluation block ignores every point, later group value, and IPA field. -/
theorem plonkProofFromJointView_evaluations_congr {actions k : ℕ} {G : Type*}
    (pub : PlonkPublicPolynomials actions) (x x1 x1' : Fp)
    (left right : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hcolumns : ∀ id : PrivateColumnId actions, ∀ i : Fin 4,
      privateColumnView left.1.2.1 id i.castSucc = privateColumnView right.1.2.1 id i.castSucc)
    (hr : left.1.2.2.1 = right.1.2.2.1) :
    plonkEvaluationStage (plonkProofFromJointView pub x x1 left) =
      plonkEvaluationStage (plonkProofFromJointView pub x x1' right) := by
  simp only [plonkEvaluationStage, plonkProofFromJointView, plonkProofString, hcolumns, hr]

section Computation

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The first four column disclosures ignore every later opening challenge and quotient callback. -/
theorem plonkMaskViewFromMaterial_early_columns {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (x x1 x2 q x1' x2' q' : Fp)
    (pieces pieces' : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions)
    (id : PrivateColumnId actions) (i : Fin 4) :
    privateColumnView (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).2.1 id i.castSucc =
      privateColumnView (plonkMaskViewFromMaterial urs pub x x1' x2' q' pieces' material).2.1 id i.castSucc := by
  change privateColumnView (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x q) material.1)
      id i.castSucc =
    privateColumnView (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x q') material.1)
      id i.castSucc
  rw [privateColumnView_observe, privateColumnView_observe]
  fin_cases i <;> rfl

/-- The early linear-mask disclosure uses x and its own coefficients only. -/
theorem plonkMaskViewFromMaterial_linearEval {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions) :
    (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).2.2.1 =
      material.2.1.1 + material.2.1.2 * x := rfl

/-- Every pre-IPA point, including Q', ignores the later opening point q. -/
theorem plonkMaskViewFromMaterial_points_q {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (x x1 x2 q q' : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions) :
    (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1 =
      (plonkMaskViewFromMaterial urs pub x x1 x2 q' pieces material).1 := rfl

/-- The emitted group scalars are evaluations of the computed opening polynomials. -/
theorem plonkMaskViewFromMaterial_groupValues {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (x x1 x2 q : Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions) :
    (plonkPreIpaProjection pub x x1
      (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material)).groupValues =
        fun i => (plonkOpeningPolynomials pub material.1 x x1 (pieces material.1) material.2.1 i).eval q :=
  honestPlonkMaskView_groupValues urs pub x x1 x2 q pieces material.1 material.2.1 material.2.2

/-- The actual evaluation-scalar stage uses no challenge after x, even through its joint view. -/
theorem plonkVerifierProofFromTape_evaluations_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (hx : left.x = right.x) (htape : TapeAgrees tape tape') :
    plonkEvaluationStage
        (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left tape) =
      plonkEvaluationStage
        (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right tape') := by
  have hmaterial := plonkJointMaterialFromTape_congr _ _ [] tape tape'
    (plonkTotalColumnConstructor_challenges vk pub witness left right htheta hbeta hgamma) htape
  unfold plonkVerifierProofFromTape
  simp only [hx]
  apply plonkProofFromJointView_evaluations_congr
  · intro id i
    change privateColumnView (plonkMaskViewFromMaterial urs pub right.x left.x1 left.x2 left.x3
        (plonkHonestQuotientPieces vk pub left) (plonkJointMaterialFromTape _ [] tape)).2.1 id i.castSucc =
      privateColumnView (plonkMaskViewFromMaterial urs pub right.x right.x1 right.x2 right.x3
        (plonkHonestQuotientPieces vk pub right) (plonkJointMaterialFromTape _ [] tape')).2.1 id i.castSucc
    rw [hmaterial]
    exact plonkMaskViewFromMaterial_early_columns _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · change (plonkMaskViewFromMaterial urs pub right.x left.x1 left.x2 left.x3
        (plonkHonestQuotientPieces vk pub left) (plonkJointMaterialFromTape _ [] tape)).2.2.1 =
      (plonkMaskViewFromMaterial urs pub right.x right.x1 right.x2 right.x3
        (plonkHonestQuotientPieces vk pub right) (plonkJointMaterialFromTape _ [] tape')).2.2.1
    rw [plonkMaskViewFromMaterial_linearEval, plonkMaskViewFromMaterial_linearEval, hmaterial]

/-- The actual multi-opening quotient commitment is fixed before x3 is received. -/
theorem plonkVerifierProofFromTape_qPrime_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (hy : left.y = right.y) (hx : left.x = right.x) (hx1 : left.x1 = right.x1) (hx2 : left.x2 = right.x2)
    (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).multiopenQPrime =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').multiopenQPrime := by
  have hmaterial := plonkJointMaterialFromTape_congr _ _ [] tape tape'
    (plonkTotalColumnConstructor_challenges vk pub witness left right htheta hbeta hgamma) htape
  have hpieces : plonkHonestQuotientPieces vk pub left = plonkHonestQuotientPieces vk pub right :=
    funext fun rows => plonkHonestQuotientPieces_challenges vk pub left right rows htheta hbeta hgamma hy
  change plonkQuotientPrimeEntry (plonkMaskViewFromMaterial urs pub left.x left.x1 left.x2 left.x3
      (plonkHonestQuotientPieces vk pub left) (plonkJointMaterialFromTape _ [] tape)).1 =
    plonkQuotientPrimeEntry (plonkMaskViewFromMaterial urs pub right.x right.x1 right.x2 right.x3
      (plonkHonestQuotientPieces vk pub right) (plonkJointMaterialFromTape _ [] tape')).1
  rw [hmaterial, hpieces, hx, hx1, hx2]
  exact congrArg plonkQuotientPrimeEntry (plonkMaskViewFromMaterial_points_q _ _ _ _ _ _ _ _ _)

/-- The five actual group evaluations use x3, but no x4 or later IPA challenge. -/
theorem plonkVerifierProofFromTape_groupValues_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (hy : left.y = right.y) (hx : left.x = right.x) (hx1 : left.x1 = right.x1) (hx3 : left.x3 = right.x3)
    (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).multiopenU =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').multiopenU := by
  have hmaterial := plonkJointMaterialFromTape_congr _ _ [] tape tape'
    (plonkTotalColumnConstructor_challenges vk pub witness left right htheta hbeta hgamma) htape
  have hpieces : plonkHonestQuotientPieces vk pub left = plonkHonestQuotientPieces vk pub right :=
    funext fun rows => plonkHonestQuotientPieces_challenges vk pub left right rows htheta hbeta hgamma hy
  change (plonkPreIpaProjection pub left.x left.x1
      (plonkMaskViewFromMaterial urs pub left.x left.x1 left.x2 left.x3
        (plonkHonestQuotientPieces vk pub left) (plonkJointMaterialFromTape _ [] tape))).groupValues =
    (plonkPreIpaProjection pub right.x right.x1
      (plonkMaskViewFromMaterial urs pub right.x right.x1 right.x2 right.x3
        (plonkHonestQuotientPieces vk pub right) (plonkJointMaterialFromTape _ [] tape'))).groupValues
  rw [plonkMaskViewFromMaterial_groupValues, plonkMaskViewFromMaterial_groupValues,
    hmaterial, hpieces, hx, hx1, hx3]

end Computation

end Zcash.Snark.ZeroKnowledge
