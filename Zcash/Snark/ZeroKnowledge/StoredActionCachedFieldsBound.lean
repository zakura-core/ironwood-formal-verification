import Zcash.Snark.ZeroKnowledge.StoredActionCachedFields

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Complete online real-prover cost, including all recomputations, cache searches, and raw reply reads. -/
def storedActionCachedFieldsCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions privateLength initialLength cacheLength replyLength : ℕ)
    (key : StoredPlonkKey) : ℕ :=
  cachedPrefixRunCostBudget 22 22 (cacheLength + 22) (16 + 65 * (initialLength + (72 * actions + 107) + 1))
    (storedActionHistoryReportCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions privateLength 22 key) 4
    (storedActionHistoryQueryCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions privateLength 22 initialLength key) (2 * replyLength + read + 1) + 1

set_option maxRecDepth 10000 in
/-- Concrete stored producers discharge every callback premise of the complete cached-execution envelope. -/
theorem storedActionCachedFieldsCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (privateFields : List Fp)
    (initial : List (TranscriptElt Fp VestaG)) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (replies : List (Fin challengeDigestCard)) :
    (storedActionCachedFieldsCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) privateFields initial cache replies).2 ≤
      storedActionCachedFieldsCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length privateFields.length initial.length cache.length replies.length (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let key := StoredPlonkKey.encode vk
  let report := storedActionHistoryReportCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key (encodeActionWitness witness) privateFields
  let query := storedActionHistoryQueryCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key (encodeActionWitness witness) privateFields initial
  let reportBudget := storedActionHistoryReportCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs.length privateFields.length 22 key
  let queryBudget := storedActionHistoryQueryCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs.length privateFields.length 22 initial.length key
  have hr (history : List (Fin challengeDigestCard)) (hl : history.length ≤ 22) :
      (report history history.length).2 ≤ reportBudget := by
    have h := storedActionHistoryReportCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs generators W U fixed sigma vk witness privateFields history history.length
    refine h.trans ?_
    unfold reportBudget storedActionHistoryReportCostBudget
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (storedActionHistoryTraceCostBudget_mono_history costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length privateFields.length history.length 22 key hl) _) _
  have hq (history : List (Fin challengeDigestCard)) (hl : history.length ≤ 22) :
      (query history history.length).2 ≤ queryBudget := by
    have h := storedActionHistoryQueryCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs generators W U fixed sigma vk witness privateFields initial history history.length
    refine h.trans ?_
    unfold queryBudget storedActionHistoryQueryCostBudget
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (storedActionHistoryTraceCostBudget_mono_history costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length privateFields.length history.length 22 key hl) _) _
  have hw (history : List (Fin challengeDigestCard)) (_hl : history.length ≤ 22) :
      (query history history.length).1.1.length + (query history history.length).1.2.length ≤
        16 + 65 * (initial.length + (72 * inputs.length + 107) + 1) :=
    storedActionHistoryQueryCosted_bytes_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key (encodeActionWitness witness) privateFields initial history history.length
  have hp (cursor : ℕ) : (getDListCosted read (0 : Fin challengeDigestCard) replies cursor).2 ≤
      2 * replies.length + read + 1 := getDListCosted_cost_le read (0 : Fin challengeDigestCard) replies cursor
  have h := cachedPrefixRunCosted_cost_le report (fun result => (protocolAttemptContinues result, 4)) query
    (getDListCosted read (0 : Fin challengeDigestCard) replies) 22 (cache.length + 22)
    (16 + 65 * (initial.length + (72 * inputs.length + 107) + 1)) reportBudget 4 queryBudget
    (2 * replies.length + read + 1) hr (fun _ => le_rfl) hq hw hp 22 [] cache 0 (by decide) (by omega)
  unfold storedActionCachedFieldsCosted
  exact Nat.add_le_add_right h 1

/-- Every returned public cache has at most twenty-two new entries. -/
theorem storedActionCachedFieldsCosted_cache_length_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (privateFields : List Fp)
    (initial : List (TranscriptElt Fp VestaG)) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (replies : List (Fin challengeDigestCard)) (result : ProverAttemptResult)
    (finalCache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hresult : (result, finalCache) ∈ (storedActionCachedFieldsCosted costs node equal read omegaAccess canonicalRead compare
      groupAdd groupScale inputs setup key witness privateFields initial cache replies).1) :
    finalCache.length ≤ cache.length + 22 := by
  have h := cachedPrefixRunCosted_cache_length_le
    (storedActionHistoryReportCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness privateFields) (fun result => (protocolAttemptContinues result, 4))
    (storedActionHistoryQueryCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness privateFields initial)
    (getDListCosted read (0 : Fin challengeDigestCard) replies) 22 [] cache 0
  unfold storedActionCachedFieldsCosted at hresult
  simp only [Option.mem_def, Option.some.injEq] at hresult
  rewrite [hresult] at h
  exact h

end Zcash.Snark.ZeroKnowledge
