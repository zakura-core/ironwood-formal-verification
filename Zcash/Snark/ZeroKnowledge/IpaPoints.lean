import Zcash.Snark.ZeroKnowledge.IpaSimulation
import Zcash.Snark.ZeroKnowledge.Randomness
import Zcash.Common.UniformMeasure

/-!
# Identity-point probabilities in the honest IPA

With ideal commitment blinds, all emitted points are jointly uniform, even at exceptional
challenges. This projection does not include the final scalars, so it does not replace the
joint transcript simulation. It provides the identity-encoding failure bound needed for
successful-attempt normalization.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp scalarFieldOrder card_Fp)
open scoped ENNReal

/-- One mask point, then one left/right pair per round. -/
abbrev IpaPointIndex (k : ℕ) := Unit ⊕ (Fin k × Bool)

/-- View the mask point and all round pairs as a single indexed family. -/
def ipaPointFamily {k : ℕ} {A : Type*} (mask : A) (rounds : Fin k → A × A) :
    IpaPointIndex k → A
  | .inl _ => mask
  | .inr (j, false) => (rounds j).1
  | .inr (j, true) => (rounds j).2

/-- Every emitted IPA point, including points that occur after a possible abort. -/
def IpaTranscript.pointFamily {k : ℕ} {F G : Type*} (view : IpaTranscript k F G) :
    IpaPointIndex k → G := ipaPointFamily view.maskCommitment view.messages

/-- Reindex the independent scalar blinds by the points they blind. -/
def ipaPointBlindsIndex {k : ℕ} {F : Type*} : IpaBlinds k F ≃ (IpaPointIndex k → F) where
  toFun blinds := ipaPointFamily blinds.1 blinds.2
  invFun values := (values (.inl ()), fun j => (values (.inr (j, false)), values (.inr (j, true))))
  left_inv _ := rfl
  right_inv values := by
    funext i
    rcases i with maskIndex | ⟨j, right⟩
    · cases maskIndex
      rfl
    · cases right <;> rfl

section Uniform

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
  [Fintype F] [Fintype G]

/-- For any fixed mask coefficients, the entire point projection is independently uniform. -/
theorem honestIpaPoints_fixed_mask {k : ℕ} (pub : IpaPublic k F G)
    (coefficients : Fin (2 ^ k) → F) (rho : F) (alphas : Fin k → F)
    (hW : Function.Bijective (fun r : F => r • pub.W)) :
    (PMF.uniformOfFintype (IpaBlinds k F)).map
        (fun blinds => (honestIpaTranscript pub coefficients rho alphas blinds).pointFamily) =
      PMF.uniformOfFintype (IpaPointIndex k → G) := by
  let cores := ipaPointFamily (commitGen pub.generators (sparseIpaCoefficients pub.point alphas))
    (ipaCoreMessages pub.z pub.U k pub.rounds (ipaMaskedVector pub coefficients alphas)
      (evalVector k pub.point) pub.generators)
  have hfactor : (fun blinds => (honestIpaTranscript pub coefficients rho alphas blinds).pointFamily) =
      blindedCommitments pub.W cores ∘ ipaPointBlindsIndex := by
    funext blinds i
    rcases i with maskIndex | ⟨j, right⟩
    · cases maskIndex
      rfl
    · cases right <;> rfl
  rw [hfactor, ← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    blindedCommitments_uniform pub.W cores hW]

/-- All honest emitted points are jointly uniform for arbitrary supplied challenges. -/
theorem idealIpaPoints_uniform {k : ℕ} (pub : IpaPublic k F G)
    (coefficients : Fin (2 ^ k) → F) (rho : F)
    (hW : Function.Bijective (fun r : F => r • pub.W)) :
    (idealIpaProver pub coefficients rho).map IpaTranscript.pointFamily =
      PMF.uniformOfFintype (IpaPointIndex k → G) := by
  rw [idealIpaProver, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  simp_rw [honestIpaPoints_fixed_mask pub coefficients rho _ hW]
  exact PMF.bind_const _ _

end Uniform

/-- Each honest emitted point has identity probability `1/p`, including at zero challenges. -/
theorem idealIpaPoint_identity_mass {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]
    {k : ℕ} (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) (i : IpaPointIndex k) :
    (idealIpaProver pub coefficients rho).toOuterMeasure {view | view.pointFamily i = 0} =
      (scalarFieldOrder : ℝ≥0∞)⁻¹ := by
  have hcard : Fintype.card G = scalarFieldOrder := by
    rw [← Fintype.card_congr (Equiv.ofBijective (fun r : Fp => r • pub.W) hW), card_Fp]
  change (idealIpaProver pub coefficients rho).toOuterMeasure
    (IpaTranscript.pointFamily ⁻¹' ((fun points => points i) ⁻¹' {0})) = _
  rw [← PMF.toOuterMeasure_map_apply, idealIpaPoints_uniform pub coefficients rho hW,
    ← PMF.toOuterMeasure_map_apply, Zcash.map_eval_uniformOfFintype,
    PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, hcard]

/-- At most `2k+1` emitted points can be the identity in a fixed-shape IPA attempt. -/
theorem idealIpa_identity_le {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]
    {k : ℕ} (pub : IpaPublic k Fp G) (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) :
    (idealIpaProver pub coefficients rho).toOuterMeasure {view | ∃ i, view.pointFamily i = 0} ≤
      ((2 * k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
  have hevent : {view : IpaTranscript k Fp G | ∃ i, view.pointFamily i = 0} =
      ⋃ i : IpaPointIndex k, {view | view.pointFamily i = 0} := by ext; simp
  rw [hevent]
  calc
    _ ≤ ∑ i : IpaPointIndex k,
        (idealIpaProver pub coefficients rho).toOuterMeasure {view | view.pointFamily i = 0} :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ = ((2 * k + 1 : ℕ) : ℝ≥0∞) / scalarFieldOrder := by
      simp_rw [idealIpaPoint_identity_mass pub coefficients rho hW]
      simp [IpaPointIndex, div_eq_mul_inv, nsmul_eq_mul, Nat.mul_comm, Nat.add_comm]

end Zcash.Snark.ZeroKnowledge
