import Zcash.Snark.ZeroKnowledge.ActionOracleAdversary
import Zcash.Snark.ZeroKnowledge.ActionOracleSimulator
import Zcash.Snark.ZeroKnowledge.OracleContinuationResources

/-!
# Oracle-state bounds for the complete Action experiment

Both experiments retain at most `q_pre + 22 + q_post` cache entries. The bound
holds on every supported execution, including failed attempts and the explicit
simulator programming failure. Simulator field draws are bounded separately by
`actionOracleSimulator_field_queryBound`.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common

/-- The actual Action attempt adds at most twenty-two new oracle entries. -/
theorem actionOracleProver_cache_length_le {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (observation : Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)))
    (hobs : observation ∈ (actionOracleProver urs hk inputs witness vkTranscriptRepr cache).support) :
    (oracleAttemptCache cache observation).length ≤ cache.length + 22 := by
  rw [actionOracleProver, PMF.mem_support_bind_iff] at hobs
  obtain ⟨privateTape, _, hobs⟩ := hobs
  rw [PMF.mem_support_map_iff] at hobs
  obtain ⟨output, houtput, rfl⟩ := hobs
  have h := cachedOracleLaw_cache_length_le _
    (actionOracleComp_queryBound urs hk inputs witness privateTape vkTranscriptRepr) cache output houtput
  simpa only [hk, oracleAttemptCache, Option.map_some, Option.getD_some] using h

/-- The public oracle simulator adds at most the same twenty-two entries, including its failure branch. -/
theorem actionOracleSimulator_cache_length_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (vkTranscriptRepr : Fp) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (observation : Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)))
    (hobs : observation ∈ (actionOracleSimulator urs hk inputs vkTranscriptRepr cache).support) :
    (oracleAttemptCache cache observation).length ≤ cache.length + 22 := by
  rw [actionOracleSimulator, PMF.mem_support_map_iff] at hobs
  obtain ⟨view, _, rfl⟩ := hobs
  have hcache := programOracleView_cache_length_le cache
    (plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) view.1 view.2.2)
  have hlog : (plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) view.1 view.2.2).2.length ≤ 22 := by
    have h := protocolOracleView_queries_length_le plonkPointCodec
      (actionOracleInitial urs vkTranscriptRepr inputs) (plonkAttemptTrace view.2.2)
      (extendDigestTape view.1) (plonkAfterChallenge (plonkChallengesFromDigests urs.k (extendDigestTape view.1)))
    simpa only [plonkAttemptTrace_challengeCount, hk] using h
  exact hcache.trans (Nat.add_le_add_left hlog cache.length)

/-- The adversary's entire real experiment respects the combined cache budget. -/
theorem actionOracleRealExperiment_cache_length_le {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (output : Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleRealExperiment adversary).support) :
    output.2.length ≤ adversary.beforeBudget + 22 + adversary.afterBudget := by
  rw [actionOracleRealExperiment, PMF.mem_support_bind_iff] at houtput
  obtain ⟨view, hview, houtput⟩ := houtput
  rw [actionOracleRealContinuation, PMF.mem_support_bind_iff] at houtput
  obtain ⟨observation, hobs, houtput⟩ := houtput
  have hpre := actionOraclePreprocessing_cache_length_le adversary view hview
  have hproof := actionOracleProver_cache_length_le urs hk view.1.request.inputs view.1.witness
    view.1.request.vkTranscriptRepr view.2 observation hobs
  have hpost := oracleAttemptContinue_cache_length_le _ view.2
    (adversary.after view.1.state view.1.request) (adversary.after_queryBound view.1.state view.1.request)
    observation output houtput
  omega

/-- The adversary's entire simulated experiment respects the same combined cache budget. -/
theorem actionOracleSimulatedExperiment_cache_length_le [Fintype VestaG] {actions : ℕ}
    {urs : URS VestaG} {hk : urs.k = 11} {Coins State Output : Type*}
    (adversary : ActionOracleAdversary (actions := actions) urs hk Coins State Output)
    (output : Output × OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (houtput : output ∈ (actionOracleSimulatedExperiment adversary).support) :
    output.2.length ≤ adversary.beforeBudget + 22 + adversary.afterBudget := by
  rw [actionOracleSimulatedExperiment, PMF.bind_map, PMF.mem_support_bind_iff] at houtput
  obtain ⟨view, hview, houtput⟩ := houtput
  dsimp only [Function.comp_def, actionOracleSimulatedContinuation, actionOraclePublicContext] at houtput
  rw [PMF.mem_support_bind_iff] at houtput
  obtain ⟨observation, hobs, houtput⟩ := houtput
  have hpre := actionOraclePreprocessing_cache_length_le adversary view hview
  have hproof := actionOracleSimulator_cache_length_le urs hk view.1.request.inputs
    view.1.request.vkTranscriptRepr view.2 observation hobs
  have hpost := oracleAttemptContinue_cache_length_le _ view.2
    (adversary.after view.1.state view.1.request) (adversary.after_queryBound view.1.state view.1.request)
    observation output houtput
  omega

end Zcash.Snark.ZeroKnowledge
