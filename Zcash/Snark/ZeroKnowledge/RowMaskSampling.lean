import Zcash.Snark.ZeroKnowledge.RowMaskRank
import Zcash.Snark.ZeroKnowledge.Sampling

/-!
# Replacement-row masking with the actual field law

The suffix rows are read in increasing row order from exactly `n - firstMasked` samples.
The joint ideal evaluation law is transferred to wide-reduced samples without conditioning
on a successful proving attempt or on Fiat–Shamir challenges.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Common
open scoped ENNReal

/-- Number the masked suffix rows in their consumption order. -/
def rowMaskIndexEquiv (n firstMasked : ℕ) :
    Fin (n - firstMasked) ≃ {i : Fin n // firstMasked ≤ i.val} where
  toFun i := ⟨⟨firstMasked + i.val, by have hi := i.isLt; omega⟩,
    by change firstMasked ≤ firstMasked + i.val; omega⟩
  invFun i := ⟨i.val.val - firstMasked, by have hi := i.val.isLt; have hm := i.property; omega⟩
  left_inv := by
    intro i
    apply Fin.ext
    simp
  right_inv := by
    intro i
    apply Subtype.ext
    apply Fin.ext
    change firstMasked + (i.val.val - firstMasked) = i.val.val
    have hm := i.property
    omega

/-- Reading an ordered field tape supplies precisely the suffix-row mask function. -/
def rowMaskTapeEquiv (n firstMasked : ℕ) : (Fin (n - firstMasked) → Fp) ≃ RowMask n firstMasked :=
  Equiv.arrowCongr (rowMaskIndexEquiv n firstMasked) (Equiv.refl Fp)

/-- Row `i` consumes tape entry `i - firstMasked`. -/
theorem rowMaskTapeEquiv_apply {n firstMasked : ℕ} (tape : Fin (n - firstMasked) → Fp)
    (i : {i : Fin n // firstMasked ≤ i.val}) :
    rowMaskTapeEquiv n firstMasked tape i =
      tape ⟨i.val.val - firstMasked, by omega⟩ := rfl

/-- Evaluate the actual masked row polynomial at all supplied observation points. -/
def rowEvaluationsFromTape {n d : ℕ} (firstMasked : ℕ) (omega : Fp)
    (points : Fin d → Fp) (witness : Fin n → Fp) (tape : Fin (n - firstMasked) → Fp) :
    Fin d → Fp :=
  fun i => (maskedRowPolynomial firstMasked omega witness
    (rowMaskTapeEquiv n firstMasked tape)).eval (points i)

/-- Uniform ordered samples give the jointly uniform evaluation vector. -/
theorem uniformTapeRowEvaluations {n firstMasked d : ℕ}
    (omega : Fp) (points : Fin d → Fp) (witness : Fin n → Fp)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin firstMasked, points i ≠ omega ^ j.val)
    (hsize : firstMasked + d ≤ n) :
    (PMF.uniformOfFintype (Fin (n - firstMasked) → Fp)).map
        (rowEvaluationsFromTape firstMasked omega points witness) =
      PMF.uniformOfFintype (Fin d → Fp) := by
  change (PMF.uniformOfFintype (Fin (n - firstMasked) → Fp)).map
      ((fun mask : RowMask n firstMasked => fun i : Fin d =>
        (maskedRowPolynomial firstMasked omega witness mask).eval (points i)) ∘
          rowMaskTapeEquiv n firstMasked) = _
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv]
  exact maskedRowPolynomial_joint_uniform omega points witness hrows hpoints haway hsize

/-- The joint evaluation vector under fresh wide-reduced suffix-row samples. -/
noncomputable def sampledRowEvaluations {n d : ℕ} (firstMasked : ℕ) (omega : Fp)
    (points : Fin d → Fp) (witness : Fin n → Fp) : PMF (Fin d → Fp) :=
  (sampleFieldsWith (n - firstMasked)
    (rowEvaluationsFromTape firstMasked omega points witness)).runFreshPMF fieldSample

/-- All disclosed evaluations together cost at most one reduction bias per sampled tail row. -/
theorem sampledRowEvaluations_error_bound {n firstMasked d : ℕ}
    (omega : Fp) (points : Fin d → Fp) (witness : Fin n → Fp)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin firstMasked, points i ≠ omega ^ j.val)
    (hsize : firstMasked + d ≤ n) :
    PMFEventBiasLE (sampledRowEvaluations firstMasked omega points witness)
        (PMF.uniformOfFintype (Fin d → Fp)) (((n - firstMasked : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE (PMF.uniformOfFintype (Fin d → Fp))
        (sampledRowEvaluations firstMasked omega points witness)
        (((n - firstMasked : ℕ) : ℝ≥0∞) * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (n - firstMasked)
    (rowEvaluationsFromTape firstMasked omega points witness)
  rw [uniformTapeRowEvaluations omega points witness hrows hpoints haway hsize] at h
  exact h

/-- Six replacement rows give joint hiding for up to six distinct advice observation points. -/
theorem advicePolynomial_joint_uniform {d : ℕ} (points : Fin d → Fp)
    (witness : Fin 2048 → Fp) (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin 2042, points i ≠ omegaOf 11 ^ j.val) (hd : d ≤ 6) :
    (PMF.uniformOfFintype (RowMask 2048 2042)).map (fun mask => fun i : Fin d =>
        (advicePolynomial witness mask).eval (points i)) =
      PMF.uniformOfFintype (Fin d → Fp) :=
  maskedRowPolynomial_joint_uniform (omegaOf 11) points witness
    (omegaOf_rows_injective 11 (by decide)) hpoints haway (by omega)

/-- Product polynomials retain row 2042 and mask the following five rows. -/
theorem productRowPolynomial_joint_uniform {d : ℕ} (points : Fin d → Fp)
    (witness : Fin 2048 → Fp) (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin 2043, points i ≠ omegaOf 11 ^ j.val) (hd : d ≤ 5) :
    (PMF.uniformOfFintype (RowMask 2048 2043)).map (fun mask => fun i : Fin d =>
        (maskedRowPolynomial 2043 (omegaOf 11) witness mask).eval (points i)) =
      PMF.uniformOfFintype (Fin d → Fp) :=
  maskedRowPolynomial_joint_uniform (omegaOf 11) points witness
    (omegaOf_rows_injective 11 (by decide)) hpoints haway (by omega)

end Zcash.Snark.ZeroKnowledge
