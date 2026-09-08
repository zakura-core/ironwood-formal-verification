import Zcash.Snark.ZeroKnowledge.ActionOracleSimulator
import Zcash.Snark.ZeroKnowledge.ActionOracleConflicts
import Zcash.Snark.ZeroKnowledge.RawFieldTape
import Zcash.Snark.ZeroKnowledge.OracleContinuation

/-!
# An oracle simulator using only uniform raw words

This implementation wide-reduces the simulator's private fields too. It reads
one fixed tape: raw challenge responses first, then one raw word per simulator
field draw. The new simulator's sampling error is charged separately from the
already proved real-prover simulation error.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS scalarFieldOrder)
open Zcash.Circuits.Action
open Zcash.Common
open scoped ENNReal

/-- Raw challenge responses followed by all wide-reduced simulator field draws. -/
def actionOracleSimulatorWordCount (actions k : ℕ) : ℕ :=
  (k + 11) + plonkSimulatorSampleCount actions k

/-- Eleven rounds consume exactly `132m + 58` raw 512-bit words in the simulator. -/
theorem actionOracleSimulatorWordCount_eleven (actions : ℕ) :
    actionOracleSimulatorWordCount actions 11 = 132 * actions + 58 := by
  rw [actionOracleSimulatorWordCount, plonkSimulatorSampleCount_eleven]
  omega

/-- Execute the complete witness-free simulator from one fixed raw-word tape. -/
def actionOracleSimulatorFromRawTape {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (tape : RawFieldTape (actionOracleSimulatorWordCount actions urs.k)) :
    Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  let parts := splitTapeEquiv (urs.k + 11) (plonkSimulatorSampleCount actions urs.k) (Fin challengeDigestCard) tape
  actionOracleSimulatorFromTapes urs hk inputs vkTranscriptRepr cache parts.1 (reduceFieldTape parts.2)

/-- The simulator law generated entirely from a finite tape of independent uniform raw words. -/
noncomputable def actionOracleWideSimulator {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard))) :=
  (PMF.uniformOfFintype (RawFieldTape (actionOracleSimulatorWordCount actions urs.k))).map
    (actionOracleSimulatorFromRawTape urs hk inputs vkTranscriptRepr cache)

/-- The one-tape implementation has exactly the corresponding sequential wide-field sampling law. -/
theorem actionOracleWideSimulator_program {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    actionOracleWideSimulator urs hk inputs vkTranscriptRepr cache =
      (PMF.uniformOfFintype (PlonkChallengeTape urs.k (Fin challengeDigestCard))).bind (fun digests =>
        (sampleFieldsWith (plonkSimulatorSampleCount actions urs.k)
          (actionOracleSimulatorFromTapes urs hk inputs vkTranscriptRepr cache digests)).runFreshPMF fieldSample) := by
  dsimp only [actionOracleWideSimulator, actionOracleSimulatorFromRawTape]
  exact splitRawFieldTape_sample_law (urs.k + 11) (plonkSimulatorSampleCount actions urs.k)
    (actionOracleSimulatorFromTapes urs hk inputs vkTranscriptRepr cache)

/-- Using wide-reduced simulator fields adds only their own complete-tape bias. -/
theorem actionOracleWideSimulator_error_bound {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    let error := plonkSimulatorSampleCount actions urs.k * challenge255Bias
    PMFEventBiasLE (actionOracleWideSimulator urs hk inputs vkTranscriptRepr cache)
        (actionOracleSimulatorProgram urs hk inputs vkTranscriptRepr cache) error ∧
      PMFEventBiasLE (actionOracleSimulatorProgram urs hk inputs vkTranscriptRepr cache)
        (actionOracleWideSimulator urs hk inputs vkTranscriptRepr cache) error := by
  rw [actionOracleWideSimulator_program, actionOracleSimulatorProgram]
  have hsample (digests : PlonkChallengeTape urs.k (Fin challengeDigestCard)) :=
    sampleFieldsWith_error_bound (plonkSimulatorSampleCount actions urs.k)
      (actionOracleSimulatorFromTapes urs hk inputs vkTranscriptRepr cache digests)
  simp_rw [← sampleFieldsWith_uniform] at hsample
  exact ⟨eventBias_bind_support _ (fun digests _ => (hsample digests).1),
    eventBias_bind_support _ (fun digests _ => (hsample digests).2)⟩

/-- The real cached-oracle prover is simulated using only raw words, with the added simulator bias explicit. -/
theorem actionOracleWide_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    let error := (plonkSimulationErrorBound actions + (cache.length : ℝ≥0∞) / scalarFieldOrder) +
      plonkSimulatorSampleCount actions urs.k * challenge255Bias
    PMFEventBiasLE (actionOracleProver urs hk inputs witness vkTranscriptRepr cache)
        (actionOracleWideSimulator urs hk inputs vkTranscriptRepr cache) error ∧
      PMFEventBiasLE (actionOracleWideSimulator urs hk inputs vkTranscriptRepr cache)
        (actionOracleProver urs hk inputs witness vkTranscriptRepr cache) error := by
  have hsim := actionOracle_cached_simulation_error_bound urs hk inputs witness hvalid hpositive hW vkTranscriptRepr cache
  have hwide := actionOracleWideSimulator_error_bound urs hk inputs vkTranscriptRepr cache
  rw [actionOracleSimulatorProgram_law urs hk inputs hW vkTranscriptRepr cache] at hwide
  exact ⟨by simpa only [add_comm] using hsim.1.trans hwide.2, hwide.1.trans hsim.2⟩

end Zcash.Snark.ZeroKnowledge
