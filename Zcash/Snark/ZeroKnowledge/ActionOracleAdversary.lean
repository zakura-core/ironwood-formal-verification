import Zcash.Snark.ZeroKnowledge.ActionOracleConflicts
import Zcash.Snark.ZeroKnowledge.OracleContinuation

/-!
# One-attempt Action simulation against a classical oracle adversary

The adversary may query the oracle before choosing the public inputs, a valid
witness, and arbitrary retained auxiliary state. The reference prover then uses
fresh independent private coins. After receiving the observed attempt, the
adversary continues querying the same oracle cache.

The simulator's continuation receives only the public request, auxiliary state,
and cache: the selected witness is erased at that boundary. The output law
retains even the final cache, a stronger observation than query access alone.
Programming failure is explicit; ordinary attempt failures retain their original
prefix and status. This is a single attempt in a programmable classical random
oracle, not an assumption about concrete BLAKE2b or shared-oracle retries.

Query budgets constrain oracle resources. No execution-time bound is asserted
for arbitrary functions supplied in the adversary record.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS scalarFieldOrder)
open Zcash.Circuits.Action
open Zcash.Common
open scoped ENNReal

/-- The public data identifying one requested Action-bundle proof. -/
structure ActionOracleRequest (actions : ℕ) where
  inputs : Fin actions → PublicInputs Fp
  vkTranscriptRepr : Fp

/-- A valid statement/witness selection, together with all auxiliary state retained by the adversary. -/
structure ActionOracleSelection {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11) (State : Type*) where
  request : ActionOracleRequest actions
  witness : Fin actions → Fin 10 → Fin 2048 → Fp
  valid : ActionZkRelation urs hk request.inputs witness
  state : State

/-- Classical adaptive oracle programs before and after a single proof request. -/
structure ActionOracleAdversary {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (Coins State Output : Type*) where
  coins : PMF Coins
  beforeBudget : ℕ
  before : Coins → OracleComp TranscriptHashAddress (Fin challengeDigestCard)
    (ActionOracleSelection (actions := actions) urs hk State)
  before_queryBound : ∀ coins, (before coins).QueryBound beforeBudget
  afterBudget : ℕ
  after : State → ActionOracleRequest actions → Option ProverAttemptResult →
    OracleComp TranscriptHashAddress (Fin challengeDigestCard) Output
  after_queryBound : ∀ state request result, (after state request result).QueryBound afterBudget

/-- Preprocessing starts from an empty oracle cache and may select the statement adaptively. -/
noncomputable def actionOraclePreprocessing {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output) :
    PMF (ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  adversary.coins.bind fun coins =>
    cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard)) (adversary.before coins) []

/-- The actual preprocessing cache has at most the adversary's stated number of prior queries. -/
theorem actionOraclePreprocessing_cache_length_le {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hview : view ∈ (actionOraclePreprocessing adversary).support) :
    view.2.length ≤ adversary.beforeBudget := by
  obtain ⟨coins, _, hcoins⟩ := (PMF.mem_support_bind_iff _ _ _).mp hview
  simpa only [List.length_nil, Nat.zero_add] using
    cachedOracleLaw_cache_length_le _ (adversary.before_queryBound coins) [] view hcoins

/-- Erase the selected witness and its validity proof before running the simulator. -/
def actionOraclePublicContext {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11} {State : Type*}
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (ActionOracleRequest actions × State) × OracleCache TranscriptHashAddress (Fin challengeDigestCard) :=
  ((view.1.request, view.1.state), view.2)

/-- The real prover and the adversary's adaptive continuation share the same oracle state. -/
noncomputable def actionOracleRealContinuation {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleProver urs hk view.1.request.inputs view.1.witness view.1.request.vkTranscriptRepr view.2).bind
    (oracleAttemptContinue (PMF.uniformOfFintype (Fin challengeDigestCard)) view.2
      (adversary.after view.1.state view.1.request))

/-- The simulated continuation takes only public inputs, auxiliary state, and the existing oracle cache. -/
noncomputable def actionOracleSimulatedContinuation [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (view : (ActionOracleRequest actions × State) × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleSimulator urs hk view.1.1.inputs view.1.1.vkTranscriptRepr view.2).bind
    (oracleAttemptContinue (PMF.uniformOfFintype (Fin challengeDigestCard)) view.2
      (adversary.after view.1.2 view.1.1))

/-- The complete real experiment, with one proof request between the adversary's two oracle phases. -/
noncomputable def actionOracleRealExperiment {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output : Type*} (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOraclePreprocessing adversary).bind (actionOracleRealContinuation adversary)

/-- The complete simulated experiment factors through the witness-erasing public context. -/
noncomputable def actionOracleSimulatedExperiment [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  ((actionOraclePreprocessing adversary).map actionOraclePublicContext).bind
    (actionOracleSimulatedContinuation adversary)

/-- The full continuation costs at most `epsilon(m) + q_pre / p` at every supported preprocessing result. -/
theorem actionOracleContinuation_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0)
    (view : ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hcache : view.2.length ≤ adversary.beforeBudget) :
    let error := plonkSimulationErrorBound actions + (adversary.beforeBudget : ℝ≥0∞) / scalarFieldOrder
    PMFEventBiasLE (actionOracleRealContinuation adversary view)
        (actionOracleSimulatedContinuation adversary (actionOraclePublicContext view)) error ∧
      PMFEventBiasLE (actionOracleSimulatedContinuation adversary (actionOraclePublicContext view))
        (actionOracleRealContinuation adversary view) error := by
  have h := actionOracle_cached_simulation_error_bound urs hk view.1.request.inputs view.1.witness
    view.1.valid hpositive hW view.1.request.vkTranscriptRepr view.2
  have hpost := oracleAttemptContinue_error_bound (PMF.uniformOfFintype (Fin challengeDigestCard)) view.2
    (adversary.after view.1.state view.1.request) h.1 h.2
  have hlength : (view.2.length : ℝ≥0∞) / scalarFieldOrder ≤
      (adversary.beforeBudget : ℝ≥0∞) / scalarFieldOrder := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_left (Nat.cast_le.mpr hcache) _
  constructor
  · intro event
    exact (hpost.1 event).trans (add_le_add le_rfl (add_le_add le_rfl hlength))
  · intro event
    exact (hpost.2 event).trans (add_le_add le_rfl (add_le_add le_rfl hlength))

/-- Single-attempt statistical simulation against adaptive classical oracle preprocessing and postprocessing. -/
theorem actionOracleAdversary_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) :
    let error := plonkSimulationErrorBound actions + (adversary.beforeBudget : ℝ≥0∞) / scalarFieldOrder
    PMFEventBiasLE (actionOracleRealExperiment adversary) (actionOracleSimulatedExperiment adversary) error ∧
      PMFEventBiasLE (actionOracleSimulatedExperiment adversary) (actionOracleRealExperiment adversary) error := by
  simp only [actionOracleRealExperiment, actionOracleSimulatedExperiment, PMF.bind_map, Function.comp_def]
  constructor
  · apply eventBias_bind_support
    intro view hview
    exact (actionOracleContinuation_error_bound adversary hpositive hW view
      (actionOraclePreprocessing_cache_length_le adversary view hview)).1
  · apply eventBias_bind_support
    intro view hview
    exact (actionOracleContinuation_error_bound adversary hpositive hW view
      (actionOraclePreprocessing_cache_length_le adversary view hview)).2

end Zcash.Snark.ZeroKnowledge
