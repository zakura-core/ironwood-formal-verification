import Zcash.Snark.ZeroKnowledge.ActionGeneratorRetry
import Zcash.Snark.ZeroKnowledge.ActionOracleRetryPrng

/-!
# Finite Action Fiat–Shamir retries from one uniform seed

The generator is initialized exactly once after adaptive preprocessing, using a
fresh uniform bit seed. Each started attempt allocates one complete private
block and then updates the same generator state. Public oracle reply slots and
postprocessing use the existing independent random-oracle law and retained cache.

The observed experiment equals the whole-prefix source game. Thus its Boolean
test advantage is at most `R(m,q,n) + eta` under security of the entire generated
prefix against the actual admitted reduction. The premise covers `n(148m+46)`
raw words, even on runs that use fewer. Concrete generator security and the
reduction's resource-class membership remain explicit assumptions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (URS)
open Zcash.Common
open scoped ENNReal

/-- Initialize one private generator after preprocessing and carry it through all started attempts. -/
noncomputable def actionGeneratedOracleRetryExperiment {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output Generator : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (next : Generator → Fin challengeDigestCard × Generator) (budget seedBits : ℕ)
    (initState : (Fin seedBits → Bool) → Generator) :
    PMF (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  (actionOracleRetryPreprocessing adversary).bind fun view =>
    (sourceTapeExperiment (PMF.uniformOfFintype (OracleReplyRetryTape urs.k budget))
      ((PMF.uniformOfFintype (Fin seedBits → Bool)).map initState)
      (fun replies generator => (actionGeneratedOracleRetries urs hk view.1.request.inputs view.1.witness
        view.1.request.vkTranscriptRepr next replies view.2 generator).1)).bind
      fun observed => cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard))
        (adversary.after view.1.state view.1.request observed.1) observed.2

/-- The continuing-generator execution has exactly the source game's full adaptive observation law. -/
theorem actionGeneratedOracleRetryExperiment_law {actions : ℕ} {urs : URS VestaG} {hk : urs.k = 11}
    {Coins State Output Generator : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (next : Generator → Fin challengeDigestCard × Generator) (budget seedBits : ℕ)
    (initState : (Fin seedBits → Bool) → Generator) :
    actionGeneratedOracleRetryExperiment adversary next budget seedBits initState =
      actionOracleRetrySourceExperiment adversary (uniformSeedTapeSource seedBits
        (fun seed => actionGeneratorRetryTape next actions budget (initState seed))) := by
  apply congrArg (PMF.bind (actionOracleRetryPreprocessing adversary))
  funext view
  have h := actionGeneratedOracleRetries_source_law urs hk view.1.request.inputs view.1.witness
    view.1.request.vkTranscriptRepr next budget
    ((PMF.uniformOfFintype (Fin seedBits → Bool)).map initState) view.2
  rw [PMF.map_comp] at h
  exact congrArg (fun law => law.bind (fun observed =>
    cachedOracleLaw (PMF.uniformOfFintype (Fin challengeDigestCard))
      (adversary.after view.1.state view.1.request observed.1) observed.2)) h

/-- The one-seed, continuing-generator implementation inherits finite retry simulation with one whole-prefix PRNG loss. -/
theorem generatedActionFiatShamirRetry_test_error_bound [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output Generator : Type*}
    (adversary : ActionOracleRetryAdversary (actions := actions) urs hk Coins State Output)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0)
    (next : Generator → Fin challengeDigestCard × Generator) (budget seedBits : ℕ)
    (initState : (Fin seedBits → Bool) → Generator)
    (test : (Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) → PMF Bool)
    (admissible : Set ((ActionOracleSelection (actions := actions) urs hk State ×
      OracleCache TranscriptHashAddress (Fin challengeDigestCard)) → RawPrivateRetryTape actions budget → PMF Bool))
    (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits
      (fun seed => actionGeneratorRetryTape next actions budget (initState seed))
      (actionOracleRetryPreprocessing adversary) admissible η)
    (hclass : actionOracleRetryPrngReduction adversary budget test ∈ admissible) :
    PMFEventBiasLE ((actionGeneratedOracleRetryExperiment adversary next budget seedBits initState).bind test)
        ((actionOracleRetrySimulatedExperiment adversary budget).bind test)
        (oracleRetryError actions adversary.beforeBudget budget + η) ∧
      PMFEventBiasLE ((actionOracleRetrySimulatedExperiment adversary budget).bind test)
        ((actionGeneratedOracleRetryExperiment adversary next budget seedBits initState).bind test)
        (oracleRetryError actions adversary.beforeBudget budget + η) := by
  rw [actionGeneratedOracleRetryExperiment_law]
  exact uniformSeedActionFiatShamirRetry_test_error_bound adversary hpositive hW budget seedBits
    (fun seed => actionGeneratorRetryTape next actions budget (initState seed)) test admissible η secure hclass

end Zcash.Snark.ZeroKnowledge
