import Zcash.Snark.ZeroKnowledge.BatchedTape
import Zcash.Snark.ZeroKnowledge.PlonkColumns
import Zcash.Snark.ZeroKnowledge.IpaSampling

/-!
# The Action-indexed sampling batches

The available Bento sampler at `e32e61eb35b6e5b5e0600cb0903adcfe0cd617d8` samples
all ten advice tails for an Action before their ten blinds, and both lookup tails before
their two blinds. Product columns use singleton batches. This module describes those
batches explicitly and proves that they flatten to the pinned column order. The separate
Sensei revision `56a7de7` remains unavailable; this is not a Rust refinement theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Common
open scoped ENNReal

/-- Ordered batches: advice per Action, input/table per lookup, then individual products. -/
def privateColumnBatches (actions : ℕ) : List (List (PrivateColumnId actions)) :=
  (List.finRange actions).map (fun a => (List.finRange 10).map (.advice a)) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 3).map
    (fun l => [.lookupInput a l, .lookupTable a l])) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 3).map
    (fun s => [.permutationProduct a s])) ++
  (List.finRange actions).flatMap (fun a => (List.finRange 3).map
    (fun l => [.lookupProduct a l]))

/-- Batching retains every private column in its commitment order. -/
theorem privateColumnBatches_flatten (actions : ℕ) :
    (privateColumnBatches actions).flatten = privateColumnOrder actions := by
  simp [privateColumnBatches, privateColumnOrder, List.flatten_eq_flatMap,
    List.flatMap_assoc, List.map_eq_flatMap]

/-- Install retained-row constructors in the concrete source batches. -/
def plonkColumnBatches {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    List (List (ColumnStep 2048)) :=
  (privateColumnBatches actions).map fun ids => ids.map fun id => ⟨id.firstMasked, construct id⟩

/-- The batched and sequential models construct exactly the same ordered columns. -/
theorem plonkColumnBatches_flatten {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    (plonkColumnBatches construct).flatten = plonkColumnSteps construct := by
  rw [plonkColumnBatches, ← List.map_flatten, privateColumnBatches_flatten]
  rfl

/-- All replacement rows and all private-column blinds consume `148m` field draws. -/
theorem plonkColumnBatches_sample_count {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    batchedColumnSampleCount (plonkColumnBatches construct) = 148 * actions := by
  rw [batchedColumnSampleCount_eq, plonkColumnBatches_flatten, columnFullSampleCount_eq,
    plonkColumnSteps_row_samples, plonkColumnSteps_length]
  omega

/-- Adding the shared masks and the eleven-round IPA recovers the description's full budget. -/
theorem plonk_and_ipa_sample_count {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    batchedColumnSampleCount (plonkColumnBatches construct) + 12 + ipaSampleCount 11 =
      fieldSampleCount actions := by
  rw [plonkColumnBatches_sample_count]
  simp [ipaSampleCount, fieldSampleCount]

section View

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- The pinned column sizes hide the complete enriched pre-IPA view under the batched sampler. -/
theorem sampledPlonkPreIpa_simulation_error_bound {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (W : G) (x q : Fp) (points : Fin 5 → Fp)
    (cores : ColumnHistory 2048 → Fp × Fp →
      Fin ((plonkColumnBatches construct).flatten.length + 10) → G)
    (offset : ColumnHistory 2048 → Fp → Fp)
    (hW : Function.Bijective (fun r : Fp => r • W))
    (hpoints : Function.Injective points)
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048, points i ≠ omegaOf 11 ^ j.val) (hq : q ≠ x) :
    PMFEventBiasLE
        (sampledBatchedPreIpa (plonkColumnBatches construct) history W (omegaOf 11) x q points cores offset)
        (preIpaMaskSimulator (G := G) 5 (22 * actions)
          ((plonkColumnBatches construct).flatten.length + 10))
        (((148 * actions + 12 : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE
        (preIpaMaskSimulator (G := G) 5 (22 * actions)
          ((plonkColumnBatches construct).flatten.length + 10))
        (sampledBatchedPreIpa (plonkColumnBatches construct) history W (omegaOf 11) x q points cores offset)
        (((148 * actions + 12 : ℕ) : ℝ≥0∞) * challenge255Bias) := by
  have hrows := omegaOf_rows_injective 11 (by decide)
  have hsize (step : ColumnStep 2048) (hstep : step ∈ (plonkColumnBatches construct).flatten) :
      step.firstMasked + 5 ≤ 2048 := by
    rw [plonkColumnBatches_flatten] at hstep
    have h := plonkColumnSteps_firstMasked_le construct step hstep
    omega
  have haway' (step : ColumnStep 2048) (hstep : step ∈ (plonkColumnBatches construct).flatten)
      (i : Fin 5) (j : Fin step.firstMasked) : points i ≠ omegaOf 11 ^ j.val :=
    haway i ⟨j.val, by have h := hsize step hstep; omega⟩
  have h := sampledBatchedPreIpa_simulation_error_bound (plonkColumnBatches construct) history W
    (omegaOf 11) x q points cores offset hW hrows hpoints haway' hsize hq
  simpa only [plonkColumnBatches_flatten, plonkColumnSteps_length,
    plonkColumnBatches_sample_count] using h

end View

end Zcash.Snark.ZeroKnowledge
