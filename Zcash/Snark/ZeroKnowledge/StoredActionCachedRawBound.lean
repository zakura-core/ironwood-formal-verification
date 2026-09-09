import Zcash.Snark.ZeroKnowledge.StoredActionCachedRawCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Complete stored-raw-tape real-prover budget, including public initialization and online cache reuse. -/
def storedActionCachedRawCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions privateLength replyLength cacheLength : ℕ)
    (key : StoredPlonkKey) : ℕ :=
  let samples := fieldSampleCount actions
  let fields := samples * (2 * privateLength + read + 4) + samples * samples + 1
  let initial := actions * (storedActionInstanceCommitmentBudget costs groupAdd groupScale read omegaAccess actions + 7) +
    actions * actions + read + 5
  fields + initial + storedActionCachedFieldsCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    actions samples (actions + 1) cacheLength replyLength key + 3

/-- The complete cached attempt has no remaining private-tape, real-prover, codec, or cache producer premise. -/
theorem storedActionCachedRawCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (privateWords replies : List (Fin challengeDigestCard)) :
    (storedActionCachedRawCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) vkTranscriptRepr cache privateWords replies).2 ≤
      storedActionCachedRawCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length privateWords.length replies.length cache.length (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let fields := storedRawFieldsCosted (fieldSampleCount inputs.length) read privateWords
  let initial := storedActionInitialCosted costs groupAdd groupScale read omegaAccess inputs setup (vkTranscriptRepr, read + 1)
  have hf := storedRawFieldsCosted_cost_le (fieldSampleCount inputs.length) read privateWords
  have hi := storedActionInitialCosted_cost_le costs groupAdd groupScale read omegaAccess inputs generators W U fixed sigma
    (vkTranscriptRepr, read + 1)
  have hr := storedActionCachedFieldsCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness fields.1 initial.1 cache replies
  have hfields : fields.1.length = fieldSampleCount inputs.length := storedRawFieldsCosted_length _ read privateWords
  have hinitial : initial.1.length = inputs.length + 1 :=
    storedActionInitialCosted_length costs groupAdd groupScale read omegaAccess inputs setup (vkTranscriptRepr, read + 1)
  rewrite [hfields, hinitial] at hr
  unfold storedActionCachedRawCosted
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hf hi) hr) 3

/-- Enlarging the prior cache can only enlarge the complete fixed-input envelope. -/
theorem storedActionCachedRawCostBudget_mono_cache (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions privateLength replyLength left right : ℕ)
    (key : StoredPlonkKey) (h : left ≤ right) :
    storedActionCachedRawCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions privateLength replyLength left key ≤
    storedActionCachedRawCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions privateLength replyLength right key := by
  unfold storedActionCachedRawCostBudget storedActionCachedFieldsCostBudget cachedPrefixRunCostBudget
  dsimp only
  gcongr

/-- Initialization and tape decoding preserve the same twenty-two-entry cache-growth bound. -/
theorem storedActionCachedRawCosted_cache_length_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (privateWords replies : List (Fin challengeDigestCard)) (result : ProverAttemptResult)
    (finalCache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hresult : (result, finalCache) ∈ (storedActionCachedRawCosted costs node equal read omegaAccess canonicalRead compare
      groupAdd groupScale inputs setup key witness vkTranscriptRepr cache privateWords replies).1) :
    finalCache.length ≤ cache.length + 22 := by
  unfold storedActionCachedRawCosted at hresult
  exact storedActionCachedFieldsCosted_cache_length_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness (storedRawFieldsCosted (fieldSampleCount inputs.length) read privateWords).1
    (storedActionInitialCosted costs groupAdd groupScale read omegaAccess inputs setup (vkTranscriptRepr, read + 1)).1
    cache replies result finalCache hresult

end Zcash.Snark.ZeroKnowledge
