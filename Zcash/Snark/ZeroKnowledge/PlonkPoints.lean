import Zcash.Snark.ZeroKnowledge.PlonkComposition
import Zcash.Snark.ZeroKnowledge.IpaPoints

/-!
# Identity-point probabilities for the complete reference prover

Every pre-IPA commitment has its own independent blind. The IPA point theorem
applies conditionally on the entire pre-IPA private state, so its inherited blind
need not be independent of that state. These point projections are valid even at
exceptional challenges and without quotient or row-correctness hypotheses.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder card_Fp URS)
open CompPoly
open scoped ENNReal

/-- An identity in either the pre-IPA commitment vector or the complete IPA point family. -/
def plonkJointPointFailure {actions k : ℕ} {G : Type*} [Zero G]
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) : Prop :=
  (∃ i, view.1.1 i = 0) ∨ ∃ i, view.2.pointFamily i = 0

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- Uniform point families have at most one inverse group order of identity mass per slot. -/
theorem uniformPointFamily_identity_le (n : ℕ) (W : G)
    (hW : Function.Bijective (fun r : Fp => r • W)) :
    (PMF.uniformOfFintype (Fin n → G)).toOuterMeasure {points | ∃ i, points i = 0} ≤
      (n : ℝ≥0∞) / scalarFieldOrder := by
  have hcard : Fintype.card G = scalarFieldOrder := by
    rw [← Fintype.card_congr (Equiv.ofBijective (fun r : Fp => r • W) hW), card_Fp]
  have hatom (i : Fin n) :
      (PMF.uniformOfFintype (Fin n → G)).toOuterMeasure {points | points i = 0} =
        (scalarFieldOrder : ℝ≥0∞)⁻¹ := by
    change (PMF.uniformOfFintype (Fin n → G)).toOuterMeasure ((fun points => points i) ⁻¹' {0}) = _
    rw [← PMF.toOuterMeasure_map_apply, Zcash.map_eval_uniformOfFintype,
      PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, hcard]
  have hevent : {points : Fin n → G | ∃ i, points i = 0} =
      ⋃ i : Fin n, {points | points i = 0} := by ext; simp
  rw [hevent]
  calc
    _ ≤ ∑ i : Fin n, (PMF.uniformOfFintype (Fin n → G)).toOuterMeasure {points | points i = 0} :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ = _ := by simp [hatom, div_eq_mul_inv, nsmul_eq_mul]

/-- All pre-IPA points are jointly uniform even if the private rows and challenges are exceptional. -/
theorem idealPlonkMaterial_points {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 q : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (idealPlonkMaterial construct history).map
        (fun material => (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1) =
      PMF.uniformOfFintype (Fin (22 * actions + 10) → G) := by
  simp only [idealPlonkMaterial, Zcash.independentProductPMF, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  change (idealColumnRows (plonkColumnSteps construct) history).bind (fun rows =>
    (PMF.uniformOfFintype (Fp × Fp)).bind (fun coefficients =>
      (PMF.uniformOfFintype (Fin (22 * actions + 10) → Fp)).map
        (blindedCommitments urs.w (plonkCommitmentCores urs pub x x1 x2 pieces rows coefficients)))) = _
  simp_rw [blindedCommitments_uniform urs.w _ hW]
  rw [PMF.bind_const, PMF.bind_const]

/-- Adding the honest IPA preserves the pre-IPA point marginal. -/
theorem idealPlonkJoint_preIpa_points {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces).map
      (fun view => view.1.1) = PMF.uniformOfFintype (Fin (22 * actions + 10) → G) := by
  rw [idealPlonkJointProver, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hconst (material : PlonkPrivateMaterial actions) :
      (idealIpaProver (plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material).1
        (plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material).2.1
        (plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material).2.2).map
          (fun _ => (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1) =
        PMF.pure (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material).1 := PMF.map_const _ _
  simp_rw [hconst]
  exact idealPlonkMaterial_points construct history urs pub x x1 x2 q pieces hW

/-- The IPA identity bound holds after averaging over all pre-IPA private material. -/
theorem idealPlonkJoint_ipa_identity_le {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces).toOuterMeasure
        {view | ∃ i, view.2.pointFamily i = 0} ≤
      ((2 * urs.k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
  rw [idealPlonkJointProver, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  calc
    _ ≤ ∑' material, idealPlonkMaterial construct history material *
        (((2 * urs.k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder) := by
      apply ENNReal.tsum_le_tsum
      intro material
      let data := plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material
      exact mul_le_mul_right (idealIpa_identity_le data.1 data.2.1 data.2.2 hW) _
    _ = _ := by rw [ENNReal.tsum_mul_right, (idealPlonkMaterial construct history).tsum_coe, one_mul]

/-- At most `22m+2k+11` emitted points can cause an identity-encoding failure. -/
theorem idealPlonkJoint_identity_le {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces).toOuterMeasure
        {view | plonkJointPointFailure view} ≤
      ((22 * actions + 2 * urs.k + 11 : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
  let law := idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces
  have hpre : law.toOuterMeasure {view | ∃ i, view.1.1 i = 0} ≤
      ((22 * actions + 10 : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
    change law.toOuterMeasure ((fun view => view.1.1) ⁻¹' {points | ∃ i, points i = 0}) ≤ _
    rw [← PMF.toOuterMeasure_map_apply]
    dsimp only [law]
    rw [idealPlonkJoint_preIpa_points construct history urs pub x x1 x2 x4 q xi z rounds pieces hW]
    exact uniformPointFamily_identity_le (22 * actions + 10) urs.w hW
  change law.toOuterMeasure
    ({view | ∃ i, view.1.1 i = 0} ∪ {view | ∃ i, view.2.pointFamily i = 0}) ≤ _
  calc
    _ ≤ law.toOuterMeasure {view | ∃ i, view.1.1 i = 0} +
        law.toOuterMeasure {view | ∃ i, view.2.pointFamily i = 0} := MeasureTheory.measure_union_le _ _
    _ ≤ (((22 * actions + 10 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((2 * urs.k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder) :=
      add_le_add hpre (idealPlonkJoint_ipa_identity_le construct history urs pub
        x x1 x2 x4 q xi z rounds pieces hW)
    _ = _ := by simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]; ring

end Zcash.Snark.ZeroKnowledge
