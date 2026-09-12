import Zcash.Snark.ZeroKnowledge.ActionOracleRetrySource
import Zcash.Snark.ZeroKnowledge.StatefulRetryStreamLaw

/-!
# The complete shared-oracle Action retry observation

A present stream entry contains an ordinary attempt (or explicit programming
failure) and the resulting oracle cache. An absent entry means that the policy
has already stopped. Thus programming failure and the absent suffix of a stopped
stream are different observations. A nonterminating run keeps every entry.

The real private tape is reduced exactly as before; the public simulator uses
its existing fixed bit tape. Both processes retain the cache across attempts.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open MeasureTheory

/-- The same raw-answer cache retained by the finite Action oracle experiment. -/
abbrev ActionRetryOracleState := OracleCache TranscriptHashAddress (Fin challengeDigestCard)

/-- A present attempted result with its retained cache, or an absent entry after stopping. -/
abbrev ActionRetryStreamEntry := Option (Option ProverAttemptResult × ActionRetryOracleState)

/-- Each individual observed attempt has the discrete measurable structure. -/
instance actionRetryStreamEntry_measurableSpace : MeasurableSpace ActionRetryStreamEntry := ⊤

/-- All events of one finite observed attempt are measurable. -/
instance actionRetryStreamEntry_discreteMeasurableSpace : DiscreteMeasurableSpace ActionRetryStreamEntry := ⟨fun _ => trivial⟩

/-- Separate uniform raw reply slots and raw private words for one real attempt. -/
abbrev ActionRetryRawTape (actions k : ℕ) :=
  PlonkChallengeTape k (Fin challengeDigestCard) × RawPrivateTape actions

/-- Execute one real raw-tape attempt, retaining its observed result and new oracle cache. -/
def actionRawOracleStep {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) (tape : ActionRetryRawTape actions urs.k) :
    Option ProverAttemptResult × ActionRetryOracleState :=
  oracleAttemptState cache (actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache (actionRawOracleTape tape))

/-- Execute one witness-free bit-tape attempt with the identical cache and stopping interface. -/
def actionBitOracleStep {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState)
    (bits : Fin (actionOracleSimulatorBitCount actions urs.k) → Bool) :
    Option ProverAttemptResult × ActionRetryOracleState :=
  oracleAttemptState cache (actionOracleSimulatorFromBits urs hk inputs vkTranscriptRepr cache bits)

/-- One raw-tape stream step has exactly the real finite attempt's transition law. -/
theorem actionRawOracleStep_law {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    (PMF.uniformOfFintype (ActionRetryRawTape actions urs.k)).map
        (actionRawOracleStep urs hk inputs witness vkTranscriptRepr cache) =
      oracleRetryTransition (actionOracleProver urs hk inputs witness vkTranscriptRepr) cache := by
  have h := congrArg (PMF.map (actionOracleRunTape urs hk inputs witness vkTranscriptRepr cache))
    (actionRawOracleTape_law actions urs.k)
  rw [actionOracleRunTape_law] at h
  have ho := congrArg (PMF.map (oracleAttemptState cache)) h
  simpa only [PMF.map_comp, Function.comp_def, actionRawOracleStep, oracleRetryTransition] using ho

/-- One bit-tape stream step has exactly the finite public simulator's transition law. -/
theorem actionBitOracleStep_law {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    (PMF.uniformOfFintype (Fin (actionOracleSimulatorBitCount actions urs.k) → Bool)).map
        (actionBitOracleStep urs hk inputs vkTranscriptRepr cache) =
      oracleRetryTransition (actionOracleBitSimulator urs hk inputs vkTranscriptRepr) cache := by
  simp only [oracleRetryTransition, actionOracleBitSimulator, PMF.map_comp, Function.comp_def]
  apply congrArg (fun run => (PMF.uniformOfFintype (Fin (actionOracleSimulatorBitCount actions urs.k) → Bool)).map run)
  rfl

/-- All real shared-oracle attempts, with possible infinite execution retained in the probability space. -/
noncomputable def actionOracleRetryStream {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) : Measure (ℕ → ActionRetryStreamEntry) :=
  statefulRetryStreamLaw (actionRawOracleStep urs hk inputs witness vkTranscriptRepr) oracleRetrySet cache

/-- The complete witness-free shared-oracle stream, driven by independent fixed-size bit tapes. -/
noncomputable def actionOracleBitRetryStream {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    Measure (ℕ → ActionRetryStreamEntry) :=
  statefulRetryStreamLaw (actionBitOracleStep urs hk inputs vkTranscriptRepr) oracleRetrySet cache

/-- The real complete-stream experiment is a probability measure without any stopping premise. -/
instance actionOracleRetryStream_isProbabilityMeasure {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    IsProbabilityMeasure (actionOracleRetryStream urs hk inputs witness vkTranscriptRepr cache) := by
  unfold actionOracleRetryStream
  infer_instance

/-- The public complete-stream experiment is also normalized before any termination theorem is applied. -/
instance actionOracleBitRetryStream_isProbabilityMeasure {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp) (cache : ActionRetryOracleState) :
    IsProbabilityMeasure (actionOracleBitRetryStream urs hk inputs vkTranscriptRepr cache) := by
  unfold actionOracleBitRetryStream
  infer_instance

end Zcash.Snark.ZeroKnowledge
