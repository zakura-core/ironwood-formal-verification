import Zcash.Snark.ZeroKnowledge.StoredActionRecordedCost
import Zcash.Snark.ZeroKnowledge.StoredActionRawStepBound
import Zcash.Snark.ZeroKnowledge.StatefulRetryCostBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- All attempts fit inside one envelope with the initial cache plus twenty-two entries per attempt. -/
def storedActionRecordedCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions budget cacheLength : ℕ)
    (key : StoredPlonkKey) : ℕ :=
  (budget + 1) * (storedActionCachedRawCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    actions (fieldSampleCount actions) 22 (cacheLength + 22 * budget) key + 28) + 1

/-- The complete retained retry execution has a fixed structural bound for every correlated private prefix.
No real-prover, state, retry-policy, or generated-history producer is assumed to be free. -/
theorem storedActionRecordedCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (tapes : List StoredActionRetryTape) (cache : ActionRetryOracleState)
    (htapes : ∀ tape ∈ tapes, tape.1.length = 22 ∧ tape.2.length = fieldSampleCount inputs.length) :
    (storedActionRecordedCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) vkTranscriptRepr tapes cache).2 ≤
      storedActionRecordedCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length tapes.length cache.length (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let key := StoredPlonkKey.encode vk
  let run := storedActionRecordedStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key (encodeActionWitness witness) vkTranscriptRepr
  let cap := cache.length + 22 * tapes.length
  let attemptPrice := storedActionCachedRawCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs.length (fieldSampleCount inputs.length) 22 cap key
  let valid := fun tape : StoredActionRetryTape => tape.1.length = 22 ∧ tape.2.length = fieldSampleCount inputs.length
  have hrun : ∀ state, state.length ≤ cap → ∀ tape, valid tape → (run state tape).2 ≤ attemptPrice + 10 := by
    intro state hs tape ht
    have h := storedActionRecordedStepCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs generators W U fixed sigma vk witness vkTranscriptRepr state tape
    rewrite [ht.1, ht.2] at h
    exact le_trans h (Nat.add_le_add_right
      (storedActionCachedRawCostBudget_mono_cache costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length (fieldSampleCount inputs.length) 22 state.length cap key hs) 10)
  have hgrowth : ∀ state tape, valid tape → (run state tape).1.2.length ≤ state.length + 22 := by
    intro state tape _
    unfold run storedActionRecordedStepCosted
    exact storedActionRawStepCosted_cache_length_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key (encodeActionWitness witness) vkTranscriptRepr state tape
  have h := runStatefulRetriesCosted_cost_le run storedActionRecordedRetryCosted List.length valid
    22 cap (attemptPrice + 10) 6 hrun hgrowth storedActionRecordedRetryCosted_cost_le tapes cache htapes le_rfl
  unfold storedActionRecordedCosted storedActionRecordedCostBudget
  exact Nat.add_le_add_right h 1

end Zcash.Snark.ZeroKnowledge
