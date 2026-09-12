import Zcash.Snark.ZeroKnowledge.StoredActionRawStepCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Returning the actual retry state adds only the explicitly counted fixed-size adapter. -/
theorem storedActionRawStepCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (tape : StoredActionRetryTape) :
    (storedActionRawStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) vkTranscriptRepr cache tape).2 ≤
      storedActionCachedRawCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length tape.2.length tape.1.length cache.length (StoredPlonkKey.encode vk) + 7 := by
  have hr := storedActionCachedRawCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness vkTranscriptRepr cache tape.2 tape.1
  have hs := oracleAttemptStateCosted_cost_le cache
    (storedActionCachedRawCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) vkTranscriptRepr cache tape.2 tape.1).1
  unfold storedActionRawStepCosted
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add hr hs) 2) (by omega)

/-- Retaining each returned state as a public observation is charged in the full step bound. -/
theorem storedActionRecordedStepCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (cache : ActionRetryOracleState) (tape : StoredActionRetryTape) :
    (storedActionRecordedStepCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) vkTranscriptRepr cache tape).2 ≤
      storedActionCachedRawCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length tape.2.length tape.1.length cache.length (StoredPlonkKey.encode vk) + 10 := by
  unfold storedActionRecordedStepCosted
  exact Nat.add_le_add_right (storedActionRawStepCosted_cost_le costs node equal read omegaAccess canonicalRead compare
    groupAdd groupScale inputs generators W U fixed sigma vk witness vkTranscriptRepr cache tape) 3

end Zcash.Snark.ZeroKnowledge
