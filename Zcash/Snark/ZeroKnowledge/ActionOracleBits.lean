import Zcash.Snark.ZeroKnowledge.ActionOracleWide
import Zcash.Snark.ZeroKnowledge.RawBits
import Zcash.Snark.ZeroKnowledge.OracleBitBounds
import Zcash.Snark.ZeroKnowledge.OracleContinuationResources

/-!
# A fixed uniform bit tape for the Action oracle simulator

The executable simulator takes a fixed tape of `512 * (132m + 58)` independent
uniform bits at eleven rounds. Its first twenty-two packed words are raw oracle replies;
the remaining words are reduced modulo `p` for its private fields. No rejection
sampling or ideal uniform-field primitive is used by this implementation.

The distributional cost of its private reductions is added to the preceding
simulator theorem. The sharper ideal-field theorem is unchanged. The bit budget
and oracle-state bound do not assert a machine-instruction running-time bound.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common

/-- The complete fixed input length of the simulator's Boolean tape. -/
def actionOracleSimulatorBitCount (actions k : ℕ) : ℕ :=
  actionOracleSimulatorWordCount actions k * 512

/-- At eleven rounds the simulator's complete tape has exactly `512 * (132m + 58)` bits. -/
theorem actionOracleSimulatorBitCount_eleven (actions : ℕ) :
    actionOracleSimulatorBitCount actions 11 = 512 * (132 * actions + 58) := by
  rw [actionOracleSimulatorBitCount, actionOracleSimulatorWordCount_eleven, Nat.mul_comm]

/-- Run the complete witness-free oracle simulator directly from its fixed Boolean tape. -/
def actionOracleSimulatorFromBits {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (bits : Fin (actionOracleSimulatorBitCount actions urs.k) → Bool) :
    Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  actionOracleSimulatorFromRawTape urs hk inputs vkTranscriptRepr cache
    (rawBitsTapeEquiv (actionOracleSimulatorWordCount actions urs.k) bits)

/-- The simulator experiment driven only by independent uniform input bits. -/
noncomputable def actionOracleBitSimulator {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard))) :=
  (PMF.uniformOfFintype (Fin (actionOracleSimulatorBitCount actions urs.k) → Bool)).map
    (actionOracleSimulatorFromBits urs hk inputs vkTranscriptRepr cache)

/-- Packing the Boolean tape realizes exactly the full raw-word simulator law. -/
theorem actionOracleBitSimulator_law {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    actionOracleBitSimulator urs hk inputs vkTranscriptRepr cache =
      actionOracleWideSimulator urs hk inputs vkTranscriptRepr cache := by
  dsimp only [actionOracleBitSimulator, actionOracleSimulatorFromBits, actionOracleWideSimulator]
  simpa only [Function.comp_def] using
    rawBitsTape_map (actionOracleSimulatorWordCount actions urs.k)
      (actionOracleSimulatorFromRawTape urs hk inputs vkTranscriptRepr cache)

/-- The actual cached-oracle prover is simulated from fixed uniform bits with the complete reduction cost. -/
theorem actionOracleBit_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMFEventBiasLE (actionOracleProver urs hk inputs witness vkTranscriptRepr cache)
        (actionOracleBitSimulator urs hk inputs vkTranscriptRepr cache)
        (plonkBitSimulationErrorBound actions cache.length) ∧
      PMFEventBiasLE (actionOracleBitSimulator urs hk inputs vkTranscriptRepr cache)
        (actionOracleProver urs hk inputs witness vkTranscriptRepr cache)
        (plonkBitSimulationErrorBound actions cache.length) := by
  rw [actionOracleBitSimulator_law]
  have h := actionOracleWide_simulation_error_bound urs hk inputs witness hvalid hpositive hW vkTranscriptRepr cache
  simpa only [plonkBitSimulationErrorBound, hk, plonkSimulatorSampleCount_eleven,
    add_assoc, add_left_comm, add_comm] using h

/-- Every fixed simulator tape adds at most twenty-two entries to the retained oracle cache. -/
theorem actionOracleSimulatorFromTapes_cache_length_le {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (digests : PlonkChallengeTape urs.k (Fin challengeDigestCard))
    (fields : Fin (plonkSimulatorSampleCount actions urs.k) → Fp) :
    (oracleAttemptCache cache
      (actionOracleSimulatorFromTapes urs hk inputs vkTranscriptRepr cache digests fields)).length ≤
      cache.length + 22 := by
  unfold actionOracleSimulatorFromTapes
  apply (programOracleView_cache_length_le _ _).trans
  apply Nat.add_le_add_left
  apply (protocolOracleView_queries_length_le _ _ _ _ _).trans
  rw [plonkAttemptTrace_challengeCount, hk]

/-- The cache bound holds for every Boolean tape, including explicit programming failure. -/
theorem actionOracleSimulatorFromBits_cache_length_le {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (bits : Fin (actionOracleSimulatorBitCount actions urs.k) → Bool) :
    (oracleAttemptCache cache
      (actionOracleSimulatorFromBits urs hk inputs vkTranscriptRepr cache bits)).length ≤ cache.length + 22 := by
  dsimp only [actionOracleSimulatorFromBits, actionOracleSimulatorFromRawTape]
  exact actionOracleSimulatorFromTapes_cache_length_le urs hk inputs vkTranscriptRepr cache _ _

/-- Every supported execution of the bit-driven simulator respects the same oracle-state budget. -/
theorem actionOracleBitSimulator_cache_length_le {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (observation : Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)))
    (hobs : observation ∈ (actionOracleBitSimulator urs hk inputs vkTranscriptRepr cache).support) :
    (oracleAttemptCache cache observation).length ≤ cache.length + 22 := by
  rw [actionOracleBitSimulator, PMF.mem_support_map_iff] at hobs
  obtain ⟨bits, _, rfl⟩ := hobs
  exact actionOracleSimulatorFromBits_cache_length_le urs hk inputs vkTranscriptRepr cache bits

end Zcash.Snark.ZeroKnowledge
