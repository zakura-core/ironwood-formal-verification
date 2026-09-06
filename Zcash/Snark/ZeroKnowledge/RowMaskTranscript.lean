import Zcash.Snark.ZeroKnowledge.RowMaskSampling
import Zcash.Snark.ZeroKnowledge.CommitmentMask

/-!
# A masked column's commitment and all its observed evaluations

The commitment uses the coefficient vector of the existing masked row polynomial and an
independent scalar blind. The joint law includes that commitment and every supplied
evaluation, so the hiding claim retains their correlations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The coefficient commitment of the actual masked row polynomial, before its fresh blind. -/
def maskedColumnCommitmentCore {n : ℕ} (generators : Fin n → G) (firstMasked : ℕ)
    (omega : Fp) (witness : Fin n → Fp) (mask : RowMask n firstMasked) : G :=
  commitGen generators fun i => (maskedRowPolynomial firstMasked omega witness mask).coeff i.val

/-- All suffix values followed by the independent commitment blind. -/
def columnTapeEquiv (n firstMasked : ℕ) :
    (Fin (n - firstMasked + 1) → Fp) ≃ (RowMask n firstMasked × (Fin 1 → Fp)) :=
  (splitTapeEquiv (n - firstMasked) 1 Fp).trans
    (Equiv.prodCongr (rowMaskTapeEquiv n firstMasked) (Equiv.refl (Fin 1 → Fp)))

/-- The final selected draw blinds the column commitment. -/
theorem columnTapeEquiv_blind {n firstMasked : ℕ} (tape : Fin (n - firstMasked + 1) → Fp) :
    (columnTapeEquiv n firstMasked tape).2 0 = tape ⟨n - firstMasked, by omega⟩ := by
  change tape ⟨n - firstMasked + 0, _⟩ = _
  congr 1

/-- Compute the column's blinded commitment and every disclosed evaluation from its coins. -/
def maskedColumnFromTape {n d : ℕ} (W : G) (generators : Fin n → G) (firstMasked : ℕ)
    (omega : Fp) (points : Fin d → Fp) (witness : Fin n → Fp)
    (tape : Fin (n - firstMasked + 1) → Fp) : G × (Fin d → Fp) :=
  let coins := columnTapeEquiv n firstMasked tape
  (maskedColumnCommitmentCore generators firstMasked omega witness coins.1 + coins.2 0 • W,
    fun i => (maskedRowPolynomial firstMasked omega witness coins.1).eval (points i))

/-- The same column computation with ideal independent suffix values and commitment blind. -/
noncomputable def idealMaskedColumn {n d : ℕ} (W : G) (generators : Fin n → G)
    (firstMasked : ℕ) (omega : Fp) (points : Fin d → Fp) (witness : Fin n → Fp) :
    PMF (G × (Fin d → Fp)) :=
  (commitmentView (F := Fp) W
    (fun mask => fun _ : Fin 1 => maskedColumnCommitmentCore generators firstMasked omega witness mask)
    (fun mask => fun i => (maskedRowPolynomial firstMasked omega witness mask).eval (points i))
    (PMF.uniformOfFintype (RowMask n firstMasked))).map fun view => (view.1 0, view.2)

/-- The ordered uniform tape realizes precisely the declared ideal column computation. -/
theorem uniformTapeMaskedColumn {n d : ℕ} (W : G) (generators : Fin n → G)
    (firstMasked : ℕ) (omega : Fp) (points : Fin d → Fp) (witness : Fin n → Fp) :
    (PMF.uniformOfFintype (Fin (n - firstMasked + 1) → Fp)).map
        (maskedColumnFromTape W generators firstMasked omega points witness) =
      idealMaskedColumn W generators firstMasked omega points witness := by
  change (PMF.uniformOfFintype (Fin (n - firstMasked + 1) → Fp)).map
      ((fun coins : RowMask n firstMasked × (Fin 1 → Fp) =>
        (maskedColumnCommitmentCore generators firstMasked omega witness coins.1 + coins.2 0 • W,
          fun i => (maskedRowPolynomial firstMasked omega witness coins.1).eval (points i))) ∘
            columnTapeEquiv n firstMasked) = _
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    ← Zcash.independentProductPMF_uniform]
  simp only [Zcash.independentProductPMF, idealMaskedColumn, commitmentView,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

/-- Joint ideal hiding of a whole column view, including its independently blinded commitment. -/
theorem maskedColumn_joint_uniform [Fintype G] {n firstMasked d : ℕ}
    (W : G) (generators : Fin n → G) (omega : Fp) (points : Fin d → Fp)
    (witness : Fin n → Fp) (hW : Function.Bijective (fun r : Fp => r • W))
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin firstMasked, points i ≠ omega ^ j.val)
    (hsize : firstMasked + d ≤ n) :
    idealMaskedColumn W generators firstMasked omega points witness =
      PMF.uniformOfFintype (G × (Fin d → Fp)) := by
  rw [idealMaskedColumn, commitmentView_eq _ _ _ _ hW,
    maskedRowPolynomial_joint_uniform omega points witness hrows hpoints haway hsize,
    Zcash.independentProductPMF_map_left _ _ (fun points : Fin 1 → G => points 0),
    Zcash.map_eval_uniformOfFintype,
    Zcash.independentProductPMF_uniform]

/-- The joint column view with the actual suffix-value and commitment-blind sampling law. -/
noncomputable def sampledMaskedColumn {n d : ℕ} (W : G) (generators : Fin n → G)
    (firstMasked : ℕ) (omega : Fp) (points : Fin d → Fp) (witness : Fin n → Fp) :
    PMF (G × (Fin d → Fp)) :=
  (sampleFieldsWith (n - firstMasked + 1)
    (maskedColumnFromTape W generators firstMasked omega points witness)).runFreshPMF fieldSample

/-- The whole column view costs one bias per suffix value and one for its commitment blind. -/
theorem sampledMaskedColumn_error_bound [Fintype G] {n firstMasked d : ℕ}
    (W : G) (generators : Fin n → G) (omega : Fp) (points : Fin d → Fp)
    (witness : Fin n → Fp) (hW : Function.Bijective (fun r : Fp => r • W))
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin d, ∀ j : Fin firstMasked, points i ≠ omega ^ j.val)
    (hsize : firstMasked + d ≤ n) :
    PMFEventBiasLE (sampledMaskedColumn W generators firstMasked omega points witness)
        (PMF.uniformOfFintype (G × (Fin d → Fp)))
        (((n - firstMasked + 1 : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE (PMF.uniformOfFintype (G × (Fin d → Fp)))
        (sampledMaskedColumn W generators firstMasked omega points witness)
        (((n - firstMasked + 1 : ℕ) : ℝ≥0∞) * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (n - firstMasked + 1)
    (maskedColumnFromTape W generators firstMasked omega points witness)
  rw [uniformTapeMaskedColumn,
    maskedColumn_joint_uniform W generators omega points witness hW hrows hpoints haway hsize] at h
  exact h

end Zcash.Snark.ZeroKnowledge
