import Zcash.Snark.ZeroKnowledge.ColumnTape
import Zcash.Snark.ZeroKnowledge.CommitmentMask
import Zcash.Snark.ZeroKnowledge.LinearMask

/-!
# Joint masking before the IPA

This view retains all private column evaluations at a supplied family of points, both
disclosures protected by the linear mask, and every independently blinded pre-IPA point.
The quotient and multi-opening commitment cores may depend on all private row values and
both linear-mask coefficients. Their blinds are independent; this is proved jointly with
the scalar disclosures rather than inferred from pointwise hiding.

The canonical tape interleaves each column's suffix and blind, then samples the two linear
coefficients, the linear-mask commitment blind, eight quotient-piece blinds, and the
multi-opening commitment blind. Retained-row constructors, unblinded commitment cores,
and the additive part of the masked group evaluation are supplied total functions.
`PlonkOpening` and `PlonkTranscript` connect the offset and scalar projection to the pinned
opening groups; the retained-row and quotient constructions remain parameters.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

/-- All pre-IPA points, the column evaluation trace, `r(x)`, and the masked `Q₀(q)`. -/
abbrev PreIpaMaskView (d commitments : ℕ) (G : Type*) :=
  (Fin commitments → G) × (List (Fin d → Fp) × (Fp × Fp))

/-- Rows and their blinds, followed by two coefficients and ten shared commitment blinds. -/
def preIpaSampleCount {n : ℕ} (steps : List (ColumnStep n)) : ℕ := columnFullSampleCount steps + 12

/-- Separate the canonical tape into row masks, linear coefficients, and all commitment blinds. -/
def preIpaCoinEquiv {n : ℕ} (steps : List (ColumnStep n)) :
    (Fin (preIpaSampleCount steps) → Fp) ≃
      ((Fin (columnRowSampleCount steps) → Fp) × ((Fp × Fp) × (Fin (steps.length + 10) → Fp))) :=
  let A := Fin (columnRowSampleCount steps) → Fp
  let B := Fin steps.length → Fp
  let C := Fp × Fp
  let D := Fin 10 → Fp
  let extra := (splitTapeEquiv 2 10 Fp).trans
    (Equiv.prodCongr (finTwoArrowEquiv Fp) (Equiv.refl D))
  let split := (splitTapeEquiv (columnFullSampleCount steps) 12 Fp).trans
    (Equiv.prodCongr (columnCoinEquiv steps) extra)
  let regroup := (Equiv.prodProdProdComm A B C D).trans (Equiv.prodAssoc A C (B × D))
  let join := Equiv.prodCongr (Equiv.refl A)
    (Equiv.prodCongr (Equiv.refl C) (splitTapeEquiv steps.length 10 Fp).symm)
  split.trans (regroup.trans join)

section View

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Compute the joint algebraic masking view from the actual private rows, coefficients, and blinds. -/
def honestPreIpaMaskView {n d commitments : ℕ} (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin commitments → G)
    (offset : ColumnHistory n → Fp → Fp)
    (rows : ColumnHistory n) (coefficients : Fp × Fp) (blinds : Fin commitments → Fp) :
    PreIpaMaskView d commitments G :=
  (blindedCommitments W (cores rows coefficients) blinds,
    (observeColumnRows omega points rows, linearMaskView x q (offset rows) coefficients))

/-- Run the canonical sampling order, retaining each column's own independent commitment blind. -/
def preIpaMaskViewFromTape {n d : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (steps.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp) (tape : Fin (preIpaSampleCount steps) → Fp) :
    PreIpaMaskView d (steps.length + 10) G :=
  let split := splitTapeEquiv (columnFullSampleCount steps) 12 Fp tape
  let columns := columnMaterialFromTape steps history split.1
  let extra := splitTapeEquiv 2 10 Fp split.2
  honestPreIpaMaskView W omega x q points cores offset columns.1 (finTwoArrowEquiv Fp extra.1)
    ((splitTapeEquiv steps.length 10 Fp).symm (columns.2, extra.2))

/-- The separating equivalence gives exactly the rows, coefficients, and blinds used in the view. -/
theorem preIpaMaskViewFromTape_factor {n d : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (steps.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp) :
    preIpaMaskViewFromTape steps history W omega x q points cores offset =
      (fun coins => honestPreIpaMaskView W omega x q points cores offset
        (columnRowsFromTape steps history coins.1) coins.2.1 coins.2.2) ∘ preIpaCoinEquiv steps := by
  funext tape
  simp only [preIpaMaskViewFromTape, columnMaterialFromTape_eq]
  rfl

/-- The ideal joint computation, with all commitment blinds separated from the other private coins. -/
noncomputable def idealPreIpaMaskView {n d commitments : ℕ} (steps : List (ColumnStep n))
    (history : ColumnHistory n) (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin commitments → G)
    (offset : ColumnHistory n → Fp → Fp) : PMF (PreIpaMaskView d commitments G) :=
  commitmentView (F := Fp) (I := Fin commitments) W (fun coins => cores coins.1 coins.2)
    (fun coins => (observeColumnRows omega points coins.1, linearMaskView x q (offset coins.1) coins.2))
    (Zcash.independentProductPMF (idealColumnRows steps history) (PMF.uniformOfFintype (Fp × Fp)))

/-- Uniform canonical samples realize the same ideal law as separated independent blinds. -/
theorem uniformTapePreIpaMaskView {n d : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (steps.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp) :
    (PMF.uniformOfFintype (Fin (preIpaSampleCount steps) → Fp)).map
        (preIpaMaskViewFromTape steps history W omega x q points cores offset) =
      idealPreIpaMaskView steps history W omega x q points cores offset := by
  rw [preIpaMaskViewFromTape_factor, ← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    ← Zcash.independentProductPMF_uniform, ← Zcash.independentProductPMF_uniform]
  rw [idealPreIpaMaskView, ← uniformTapeColumnRows steps history]
  simp only [Zcash.independentProductPMF, commitmentView, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, PMF.bind_bind, Function.comp_def, honestPreIpaMaskView]

/-- The scalar disclosure law, retaining every column's evaluations and both linear-mask values. -/
theorem preIpaScalarView_uniform {n d : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (omega x q : Fp) (points : Fin d → Fp) (offset : ColumnHistory n → Fp → Fp)
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ step ∈ steps, ∀ i : Fin d, ∀ j : Fin step.firstMasked, points i ≠ omega ^ j.val)
    (hsize : ∀ step ∈ steps, step.firstMasked + d ≤ n) (hq : q ≠ x) :
    (Zcash.independentProductPMF (idealColumnRows steps history) (PMF.uniformOfFintype (Fp × Fp))).map
        (fun coins => (observeColumnRows omega points coins.1, linearMaskView x q (offset coins.1) coins.2)) =
      Zcash.independentProductPMF (uniformColumnViews d steps.length) (PMF.uniformOfFintype (Fp × Fp)) := by
  rw [Zcash.independentProductPMF, PMF.map_bind]
  have hfixed (rows : ColumnHistory n) :
      ((PMF.uniformOfFintype (Fp × Fp)).map (Prod.mk rows)).map
          (fun coins => (observeColumnRows omega points coins.1, linearMaskView x q (offset coins.1) coins.2)) =
        (PMF.uniformOfFintype (Fp × Fp)).map (Prod.mk (observeColumnRows omega points rows)) := by
    rw [PMF.map_comp]
    change (PMF.uniformOfFintype (Fp × Fp)).map
      (Prod.mk (observeColumnRows omega points rows) ∘ linearMaskView x q (offset rows)) = _
    rw [← PMF.map_comp, linearMaskView_uniform x q (offset rows) hq]
  simp_rw [hfixed]
  rw [← idealColumnRows_joint_uniform steps history omega points hrows hpoints haway hsize,
    Zcash.independentProductPMF, PMF.bind_map]
  rfl

/-- The public-input simulator law for this enriched pre-IPA view. -/
noncomputable def preIpaMaskSimulator [Fintype G] (d columns commitments : ℕ) :
    PMF (PreIpaMaskView d commitments G) :=
  Zcash.independentProductPMF (PMF.uniformOfFintype (Fin commitments → G))
    (Zcash.independentProductPMF (uniformColumnViews d columns) (PMF.uniformOfFintype (Fp × Fp)))

/-- All pre-IPA commitment points and scalar disclosures are simulated jointly under ideal coins. -/
theorem idealPreIpaMask_simulation_capstone [Fintype G] {n d commitments : ℕ}
    (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin commitments → G)
    (offset : ColumnHistory n → Fp → Fp)
    (hW : Function.Bijective (fun r : Fp => r • W))
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ step ∈ steps, ∀ i : Fin d, ∀ j : Fin step.firstMasked, points i ≠ omega ^ j.val)
    (hsize : ∀ step ∈ steps, step.firstMasked + d ≤ n) (hq : q ≠ x) :
    idealPreIpaMaskView steps history W omega x q points cores offset =
      preIpaMaskSimulator (G := G) d steps.length commitments := by
  rw [idealPreIpaMaskView, commitmentView_eq _ _ _ _ hW,
    preIpaScalarView_uniform steps history omega x q points offset hrows hpoints haway hsize hq]
  rfl

/-- The wide-reduced field law applied to the canonical pre-IPA sampling program. -/
noncomputable def sampledPreIpaMaskView {n d : ℕ} (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (steps.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp) : PMF (PreIpaMaskView d (steps.length + 10) G) :=
  (sampleFieldsWith (preIpaSampleCount steps)
    (preIpaMaskViewFromTape steps history W omega x q points cores offset)).runFreshPMF fieldSample

/-- Joint pre-IPA simulation costs one sampling bias per draw, including all commitment blinds. -/
theorem sampledPreIpaMask_simulation_error_bound [Fintype G] {n d : ℕ}
    (steps : List (ColumnStep n)) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (steps.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp)
    (hW : Function.Bijective (fun r : Fp => r • W))
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ step ∈ steps, ∀ i : Fin d, ∀ j : Fin step.firstMasked, points i ≠ omega ^ j.val)
    (hsize : ∀ step ∈ steps, step.firstMasked + d ≤ n) (hq : q ≠ x) :
    PMFEventBiasLE (sampledPreIpaMaskView steps history W omega x q points cores offset)
        (preIpaMaskSimulator (G := G) d steps.length (steps.length + 10))
        (preIpaSampleCount steps * challenge255Bias) ∧
      PMFEventBiasLE (preIpaMaskSimulator (G := G) d steps.length (steps.length + 10))
        (sampledPreIpaMaskView steps history W omega x q points cores offset)
        (preIpaSampleCount steps * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (preIpaSampleCount steps)
    (preIpaMaskViewFromTape steps history W omega x q points cores offset)
  rw [uniformTapePreIpaMaskView, idealPreIpaMask_simulation_capstone steps history W omega x q points
    cores offset hW hrows hpoints haway hsize hq] at h
  exact h

end View

end Zcash.Snark.ZeroKnowledge
