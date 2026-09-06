import Zcash.Snark.ZeroKnowledge.PreIpaMask

/-!
# Batched sampling of column tails and blinds

A batch samples every column's tail, then every column's commitment blind. This matches
the advice and lookup batching in the available Bento randomness sampler. The singleton
case covers permutation and lookup products. Each block is converted by a checked
equivalence to the canonical column tape; blocks and their fields retain their order.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

/-- Canonical column budgets add when two schedules are concatenated. -/
theorem columnFullSampleCount_append {n : ℕ} (first rest : List (ColumnStep n)) :
    columnFullSampleCount (first ++ rest) = columnFullSampleCount first + columnFullSampleCount rest := by
  induction first with
  | nil => simp [columnFullSampleCount]
  | cons step first ih => simp [columnFullSampleCount, ih, Nat.add_assoc]

/-- Reorder one batch from all tails followed by all blinds into the canonical column tape. -/
def batchToColumnTape {n : ℕ} (steps : List (ColumnStep n)) :
    (Fin (columnRowSampleCount steps + steps.length) → Fp) ≃ (Fin (columnFullSampleCount steps) → Fp) :=
  (splitTapeEquiv (columnRowSampleCount steps) steps.length Fp).trans (columnCoinEquiv steps).symm

/-- Every tail entry and every blind is preserved in its own subsequence by batch conversion. -/
theorem batchToColumnTape_fields {n : ℕ} (steps : List (ColumnStep n))
    (tape : Fin (columnRowSampleCount steps + steps.length) → Fp) :
    columnCoinEquiv steps (batchToColumnTape steps tape) =
      splitTapeEquiv (columnRowSampleCount steps) steps.length Fp tape :=
  (columnCoinEquiv steps).apply_symm_apply _

/-- The full number of samples in the supplied ordered batches. -/
def batchedColumnSampleCount {n : ℕ} : List (List (ColumnStep n)) → ℕ
  | [] => 0
  | block :: rest => (columnRowSampleCount block + block.length) + batchedColumnSampleCount rest

/-- Batching changes sample order but not the total number of draws. -/
theorem batchedColumnSampleCount_eq {n : ℕ} (batches : List (List (ColumnStep n))) :
    batchedColumnSampleCount batches = columnFullSampleCount batches.flatten := by
  induction batches with
  | nil => rfl
  | cons block rest ih =>
    change (columnRowSampleCount block + block.length) + batchedColumnSampleCount rest =
      columnFullSampleCount (block ++ rest.flatten)
    rw [columnFullSampleCount_append, ih, columnFullSampleCount_eq block]

/-- Convert each source batch and concatenate its canonical field tape without moving blocks. -/
def batchedToColumnTape {n : ℕ} : (batches : List (List (ColumnStep n))) →
    (Fin (batchedColumnSampleCount batches) → Fp) ≃ (Fin (columnFullSampleCount batches.flatten) → Fp)
  | [] => Equiv.refl _
  | block :: rest =>
    let split := (splitTapeEquiv (columnRowSampleCount block + block.length)
      (batchedColumnSampleCount rest) Fp).trans
        (Equiv.prodCongr (batchToColumnTape block) (batchedToColumnTape rest))
    let join := (splitTapeEquiv (columnFullSampleCount block) (columnFullSampleCount rest.flatten) Fp).symm
    let adjust := Equiv.cast (congrArg (fun count => Fin count → Fp)
      (columnFullSampleCount_append block rest.flatten).symm)
    split.trans (join.trans adjust)

/-- Preserve the twelve shared draws after converting the private-column batches. -/
def batchedPreIpaTapeEquiv {n : ℕ} (batches : List (List (ColumnStep n))) :
    (Fin (batchedColumnSampleCount batches + 12) → Fp) ≃ (Fin (preIpaSampleCount batches.flatten) → Fp) :=
  (splitTapeEquiv (batchedColumnSampleCount batches) 12 Fp).trans
    ((Equiv.prodCongr (batchedToColumnTape batches) (Equiv.refl (Fin 12 → Fp))).trans
      (splitTapeEquiv (columnFullSampleCount batches.flatten) 12 Fp).symm)

section View

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Compute the joint pre-IPA view from the batched, up-front sampling schedule. -/
def batchedPreIpaViewFromTape {n d : ℕ} (batches : List (List (ColumnStep n))) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (batches.flatten.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp) (tape : Fin (batchedColumnSampleCount batches + 12) → Fp) :
    PreIpaMaskView d (batches.flatten.length + 10) G :=
  preIpaMaskViewFromTape batches.flatten history W omega x q points cores offset (batchedPreIpaTapeEquiv batches tape)

/-- Uniform batched samples give the already proved joint honest law. -/
theorem uniformTapeBatchedPreIpa {n d : ℕ} (batches : List (List (ColumnStep n))) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (batches.flatten.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp) :
    (PMF.uniformOfFintype (Fin (batchedColumnSampleCount batches + 12) → Fp)).map
        (batchedPreIpaViewFromTape batches history W omega x q points cores offset) =
      idealPreIpaMaskView batches.flatten history W omega x q points cores offset := by
  change (PMF.uniformOfFintype (Fin (batchedColumnSampleCount batches + 12) → Fp)).map
    (preIpaMaskViewFromTape batches.flatten history W omega x q points cores offset ∘ batchedPreIpaTapeEquiv batches) = _
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv, uniformTapePreIpaMaskView]

/-- The batched program under independent wide-reduced field samples. -/
noncomputable def sampledBatchedPreIpa {n d : ℕ} (batches : List (List (ColumnStep n)))
    (history : ColumnHistory n) (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (batches.flatten.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp) : PMF (PreIpaMaskView d (batches.flatten.length + 10) G) :=
  (sampleFieldsWith (batchedColumnSampleCount batches + 12)
    (batchedPreIpaViewFromTape batches history W omega x q points cores offset)).runFreshPMF fieldSample

/-- Joint simulation of the batched program with one reduction-bias charge per actual draw. -/
theorem sampledBatchedPreIpa_simulation_error_bound [Fintype G] {n d : ℕ}
    (batches : List (List (ColumnStep n))) (history : ColumnHistory n)
    (W : G) (omega x q : Fp) (points : Fin d → Fp)
    (cores : ColumnHistory n → Fp × Fp → Fin (batches.flatten.length + 10) → G)
    (offset : ColumnHistory n → Fp → Fp)
    (hW : Function.Bijective (fun r : Fp => r • W))
    (hrows : Function.Injective fun i : Fin n => omega ^ i.val)
    (hpoints : Function.Injective points)
    (haway : ∀ step ∈ batches.flatten, ∀ i : Fin d, ∀ j : Fin step.firstMasked, points i ≠ omega ^ j.val)
    (hsize : ∀ step ∈ batches.flatten, step.firstMasked + d ≤ n) (hq : q ≠ x) :
    PMFEventBiasLE (sampledBatchedPreIpa batches history W omega x q points cores offset)
        (preIpaMaskSimulator (G := G) d batches.flatten.length (batches.flatten.length + 10))
        (((batchedColumnSampleCount batches + 12 : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE (preIpaMaskSimulator (G := G) d batches.flatten.length (batches.flatten.length + 10))
        (sampledBatchedPreIpa batches history W omega x q points cores offset)
        (((batchedColumnSampleCount batches + 12 : ℕ) : ℝ≥0∞) * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (batchedColumnSampleCount batches + 12)
    (batchedPreIpaViewFromTape batches history W omega x q points cores offset)
  rw [uniformTapeBatchedPreIpa, idealPreIpaMask_simulation_capstone batches.flatten history W omega x q points
    cores offset hW hrows hpoints haway hsize hq] at h
  exact h

end View

end Zcash.Snark.ZeroKnowledge
