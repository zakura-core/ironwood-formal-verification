import Zcash.Snark.ZeroKnowledge.ActionOracleStreamSimulation
import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamTail

/-!
# Stopping and truncation for the complete shared-oracle Action history

The public bit simulator stops almost surely. The real shared-oracle process
can have nontermination mass up to the proved simulation bound; it is neither
discarded nor assumed zero. Truncation retains every available failed prefix
and pays its actual exhaustion probability.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open MeasureTheory
open scoped ENNReal

/-- The complete shared-oracle simulator terminates almost surely under its checked retry-rate premise. -/
theorem actionOracleBitRetryStream_nontermination_eq_zero [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache) retryStreamNontermination = 0 := by
  apply le_antisymm _ bot_le
  apply statefulRetryStreamLaw_nontermination_le_of_tail _ oracleRetrySet cache (actionOracleRetryRate actions) 0
    (hhalf.trans_lt (ENNReal.half_lt_self (by norm_num) (by norm_num)))
  intro budget
  simp_rw [actionBitOracleStep_law]
  simpa only [add_zero] using statefulRetryRecorded_exhaustion_le
    (oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr)) oracleRetrySet
    (actionOracleRetryRate actions) (actionOracleBitSimulator_retry_le urs hk inputs witness hvalid hW vkTranscriptRepr)
    budget cache

/-- Possible infinite real histories have total mass no larger than the complete simulation error. -/
theorem actionOracleRetryStream_nontermination_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    (actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache) retryStreamNontermination ≤
      oracleRetryPotential actions cache.length := by
  have h := (actionOracleRetryStream_simulation_error_bound urs hk inputs witness hvalid hpositive hW hhalf
    vkTranscriptRepr cache).1 retryStreamNontermination retryStreamNontermination_measurable
  rw [actionOracleBitRetryStream_nontermination_eq_zero urs hk inputs witness hvalid hW hhalf, zero_add] at h
  exact h

/-- Clipping the simulator after a finite budget loses at most its geometric exhaustion tail. -/
theorem actionOracleBitRetryStream_truncation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp) (budget : ℕ) (cache : ActionRetryOracleState) :
    MeasureEventBiasLE (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache)
        ((actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache).map (truncateRetryStream budget))
        (actionOracleRetryRate actions ^ budget) ∧
      MeasureEventBiasLE ((actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache).map (truncateRetryStream budget))
        (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache) (actionOracleRetryRate actions ^ budget) := by
  have h := statefulRetryStreamLaw_truncation_error_bound (actionBitOracleStep urs hk inputs vkTranscriptRepr)
    oracleRetrySet budget cache
  simp_rw [actionBitOracleStep_law] at h
  have hb := statefulRetryRecorded_exhaustion_le
    (oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr)) oracleRetrySet
    (actionOracleRetryRate actions) (actionOracleBitSimulator_retry_le urs hk inputs witness hvalid hW vkTranscriptRepr)
    budget cache
  exact ⟨fun event he => (h.1 event he).trans (add_le_add le_rfl hb),
    fun event he => (h.2 event he).trans (add_le_add le_rfl hb)⟩

/-- Real truncation retains its possible nonterminating mass in the exhaustion cost. -/
theorem actionOracleRetryStream_truncation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (hhalf : actionOracleRetryRate actions ≤ 1 / 2)
    (vkTranscriptRepr : Fp) (budget : ℕ) (cache : ActionRetryOracleState) :
    let error := actionOracleRetryRate actions ^ budget + oracleRetryPotential actions cache.length
    MeasureEventBiasLE (actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache)
        ((actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache).map (truncateRetryStream budget)) error ∧
      MeasureEventBiasLE ((actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache).map (truncateRetryStream budget))
        (actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache) error := by
  have h := statefulRetryStreamLaw_truncation_error_bound (actionRawOracleStep urs hk inputs witness vkTranscriptRepr)
    oracleRetrySet budget cache
  simp_rw [actionRawOracleStep_law] at h
  have hc := (actionOracleRetryRecorded_error_bound urs hk inputs witness hvalid hpositive hW hhalf
    vkTranscriptRepr budget cache).1 {output | output.1.exhausted = true}
  have hb := statefulRetryRecorded_exhaustion_le
    (oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr)) oracleRetrySet
    (actionOracleRetryRate actions) (actionOracleBitSimulator_retry_le urs hk inputs witness hvalid hW vkTranscriptRepr)
    budget cache
  have ht := hc.trans (add_le_add hb le_rfl)
  exact ⟨fun event he => (h.1 event he).trans (add_le_add le_rfl ht),
    fun event he => (h.2 event he).trans (add_le_add le_rfl ht)⟩

end Zcash.Snark.ZeroKnowledge
