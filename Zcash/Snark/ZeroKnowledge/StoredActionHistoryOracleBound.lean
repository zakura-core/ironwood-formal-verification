import Zcash.Snark.ZeroKnowledge.StoredActionHistoryOracleCost
import Zcash.Snark.ZeroKnowledge.TranscriptByteSize

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Full real-prover recomputation and canonical observation at any received-history stage. -/
def storedActionHistoryReportCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions privateLength historyLength : ℕ)
    (key : StoredPlonkKey) : ℕ :=
  let width := 72 * actions + 107
  let observe := 22 * (read + 55 + 2) + 11 * 11 + 15 +
    width * (read + 55 + 4 * 11 + 2 * read + 3 * equal + 3600) + 4 * width + 7
  storedActionHistoryTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    actions privateLength historyLength key + observe + 2

/-- Full real-prover recomputation and original byte-address construction at one stage. -/
def storedActionHistoryQueryCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions privateLength historyLength initialLength : ℕ)
    (key : StoredPlonkKey) : ℕ :=
  let width := 72 * actions + 107
  let query := 2 * initialLength + 5 * width +
    (initialLength + width + 1) * (64 * (read + 71) + 2154) + 30
  storedActionHistoryTraceCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    actions privateLength historyLength key + query + 2

/-- The bound pays for the entire real report producer, including generated challenges and codecs. -/
theorem storedActionHistoryReportCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (privateFields : List Fp) (history : List (Fin challengeDigestCard)) (index : ℕ) :
    (storedActionHistoryReportCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) privateFields history index).2 ≤
      storedActionHistoryReportCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length privateFields.length history.length (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let produced := storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) privateFields history
  have hs := storedActionHistoryTraceCosted_length_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) privateFields history
  have hr := storedActionHistoryTraceCosted_readBound costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) privateFields history
  have hp := storedActionHistoryTraceCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness privateFields history
  have ho := canonicalProtocolOracleReportCosted_cost_le equal read produced.1.1 produced.1.2 index (read + 55) hr
  have hf : (canonicalProtocolOracleReportCosted equal read produced.1.1 produced.1.2 index).2 ≤
      22 * (read + 55 + 2) + 11 * 11 + 15 +
        (72 * inputs.length + 107) * (read + 55 + 4 * 11 + 2 * read + 3 * equal + 3600) +
        4 * (72 * inputs.length + 107) + 7 := ho.trans (by gcongr)
  unfold storedActionHistoryReportCosted
  exact Nat.add_le_add_right (Nat.add_le_add hp hf) 2

/-- Query generation is bounded by the complete real computation and all personalized query bytes. -/
theorem storedActionHistoryQueryCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (privateFields : List Fp) (initial : List (TranscriptElt Fp VestaG))
    (history : List (Fin challengeDigestCard)) (index : ℕ) :
    (storedActionHistoryQueryCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) privateFields initial history index).2 ≤
      storedActionHistoryQueryCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length privateFields.length history.length initial.length (StoredPlonkKey.encode vk) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let produced := storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) privateFields history
  have hs := storedActionHistoryTraceCosted_length_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) privateFields history
  have hp := storedActionHistoryTraceCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness privateFields history
  have hq := protocolQueryAddressCosted_cost_le read initial produced.1.2 index
  have hf : (protocolQueryAddressCosted read initial produced.1.2 index).2 ≤
      2 * initial.length + 5 * (72 * inputs.length + 107) +
        (initial.length + (72 * inputs.length + 107) + 1) * (64 * (read + 71) + 2154) + 30 := hq.trans (by gcongr)
  unfold storedActionHistoryQueryCosted
  exact Nat.add_le_add_right (Nat.add_le_add hp hf) 2

/-- Every materialized query has a fixed public byte capacity, including unsuccessful histories. -/
theorem storedActionHistoryQueryCosted_bytes_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (privateFields : List Fp)
    (initial : List (TranscriptElt Fp VestaG)) (history : List (Fin challengeDigestCard)) (index : ℕ) :
    let query := (storedActionHistoryQueryCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness privateFields initial history index).1
    query.1.length + query.2.length ≤ 16 + 65 * (initial.length + (72 * inputs.length + 107) + 1) := by
  let produced := storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness privateFields history
  have hs := storedActionHistoryTraceCosted_length_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness privateFields history
  have hq := protocolQueryAddress_bytes_le initial produced.1.2 index
  unfold storedActionHistoryQueryCosted
  simp only [protocolQueryAddressCosted_result]
  exact hq.trans (by gcongr)

end Zcash.Snark.ZeroKnowledge
