import Zcash.Snark.ZeroKnowledge.ActionOracleBits
import Zcash.Snark.ZeroKnowledge.ActionFiatShamir

/-!
# One-attempt Action Fiat–Shamir simulation using only fixed bit tapes

The reference prover and the oracle experiment are unchanged. This simulator
uses `512 * (132m + 58)` fresh independent uniform bits and wide reduction for
all its private field draws. Its continuation receives only the public request,
retained auxiliary state, and oracle cache, with the witness erased.

For a positive Action count, the full adaptive experiment has two-sided error
`(42882m + 4113 + q_pre) / p + (280m + 106) delta`, strictly less than
`m * 2^-238 + q_pre / p`. All prior theorem premises, failure observations, and
the actual verifier query schedule are retained. The oracle remains a
programmable classical random oracle; concrete hash security and shared-oracle
retries are separate claims.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (URS scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- The bit-tape simulator and adaptive postprocessing use only the public context and retained oracle state. -/
noncomputable def actionOracleBitSimulatedContinuation {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (view : (ActionOracleRequest actions × State) × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleBitSimulator urs hk view.1.1.inputs view.1.1.vkTranscriptRepr view.2).bind
    (oracleAttemptContinue (PMF.uniformOfFintype (Fin challengeDigestCard)) view.2
      (adversary.after view.1.2 view.1.1))

/-- The complete simulated experiment erases the witness before sampling its fresh fixed bit tape. -/
noncomputable def actionOracleBitSimulatedExperiment {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  ((actionOraclePreprocessing adversary).map actionOraclePublicContext).bind
    (actionOracleBitSimulatedContinuation adversary)

/-- The bit-simulator comparison survives every adaptive post-proof oracle computation. -/
theorem actionOracleBitContinuation_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0)
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hcache : view.2.length ≤ adversary.beforeBudget) :
    PMFEventBiasLE (actionOracleRealContinuation adversary view)
        (actionOracleBitSimulatedContinuation adversary (actionOraclePublicContext view))
        (plonkBitSimulationErrorBound actions adversary.beforeBudget) ∧
      PMFEventBiasLE (actionOracleBitSimulatedContinuation adversary (actionOraclePublicContext view))
        (actionOracleRealContinuation adversary view)
        (plonkBitSimulationErrorBound actions adversary.beforeBudget) := by
  have h := actionOracleBit_simulation_error_bound urs hk view.1.request.inputs view.1.witness
    view.1.valid hpositive hW view.1.request.vkTranscriptRepr view.2
  have hpost := oracleAttemptContinue_error_bound (PMF.uniformOfFintype (Fin challengeDigestCard)) view.2
    (adversary.after view.1.state view.1.request) h.1 h.2
  have hbudget := plonkBitSimulationErrorBound_mono_queries actions hcache
  constructor
  · intro event
    exact (hpost.1 event).trans (add_le_add le_rfl hbudget)
  · intro event
    exact (hpost.2 event).trans (add_le_add le_rfl hbudget)

/-- Statistical Fiat–Shamir simulation by a fixed-bit-tape simulator, retaining the entire final oracle view. -/
theorem actionFiatShamirBits_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) :
    PMFEventBiasLE (actionOracleRealExperiment adversary) (actionOracleBitSimulatedExperiment adversary)
        (plonkBitSimulationErrorBound actions adversary.beforeBudget) ∧
      PMFEventBiasLE (actionOracleBitSimulatedExperiment adversary) (actionOracleRealExperiment adversary)
        (plonkBitSimulationErrorBound actions adversary.beforeBudget) := by
  simp only [actionOracleRealExperiment, actionOracleBitSimulatedExperiment, PMF.bind_map, Function.comp_def]
  constructor
  · apply eventBias_bind_support
    intro view hview
    exact (actionOracleBitContinuation_error_bound adversary hpositive hW view
      (actionOraclePreprocessing_cache_length_le adversary view hview)).1
  · apply eventBias_bind_support
    intro view hview
    exact (actionOracleBitContinuation_error_bound adversary hpositive hW view
      (actionOraclePreprocessing_cache_length_le adversary view hview)).2

/-- The full bit-simulator experiment retains the readable `m * 2^-238 + q_pre / p` event bound. -/
theorem actionFiatShamirBits_binary_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) :
    let error := actions * (1 / (2 : ℝ≥0∞) ^ 238) + (adversary.beforeBudget : ℝ≥0∞) / scalarFieldOrder
    PMFEventBiasLE (actionOracleRealExperiment adversary) (actionOracleBitSimulatedExperiment adversary) error ∧
      PMFEventBiasLE (actionOracleBitSimulatedExperiment adversary) (actionOracleRealExperiment adversary) error := by
  have h := actionFiatShamirBits_simulation_error_bound adversary hpositive hW
  have hbudget := (plonkBitSimulationErrorBound_lt_actions_mul_two_pow hpositive adversary.beforeBudget).le
  exact ⟨fun event => (h.1 event).trans (add_le_add le_rfl hbudget),
    fun event => (h.2 event).trans (add_le_add le_rfl hbudget)⟩

/-- Including adaptive preprocessing and postprocessing, the bit simulator retains at most `q_pre + 22 + q_post` entries. -/
theorem actionOracleBitSimulatedExperiment_cache_length_le {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (output : Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleBitSimulatedExperiment adversary).support) :
    output.2.length ≤ adversary.beforeBudget + 22 + adversary.afterBudget := by
  rw [actionOracleBitSimulatedExperiment, PMF.bind_map, PMF.mem_support_bind_iff] at houtput
  obtain ⟨view, hview, houtput⟩ := houtput
  dsimp only [Function.comp_def, actionOracleBitSimulatedContinuation, actionOraclePublicContext] at houtput
  rw [PMF.mem_support_bind_iff] at houtput
  obtain ⟨observation, hobs, houtput⟩ := houtput
  have hpre := actionOraclePreprocessing_cache_length_le adversary view hview
  have hproof := actionOracleBitSimulator_cache_length_le urs hk view.1.request.inputs
    view.1.request.vkTranscriptRepr view.2 observation hobs
  have hpost := oracleAttemptContinue_cache_length_le _ view.2
    (adversary.after view.1.state view.1.request) (adversary.after_queryBound view.1.state view.1.request)
    observation output houtput
  omega

end Zcash.Snark.ZeroKnowledge
