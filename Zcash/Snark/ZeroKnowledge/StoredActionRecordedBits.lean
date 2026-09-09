import Zcash.Snark.ZeroKnowledge.StoredActionRecordedBound
import Zcash.Snark.ZeroKnowledge.StoredRawMatrixCost
import Zcash.Snark.ZeroKnowledge.StoredRetryTapePairing

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
attribute [local irreducible] actionReferenceKey

/-- The actual full retry reduction receives a stored private prefix and a separate stored fair-bit tape. -/
@[irreducible] def storedActionRecordedBitsCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (vkTranscriptRepr : Fp) (budget : ℕ)
    (bits : List Bool) (privateRows : List (List (Fin challengeDigestCard)))
    (cache : ActionRetryOracleState) : ActionRetryRecordedView × ℕ :=
  let replies := storedRawMatrixCosted budget 22 read bits
  let tapes := zipListCosted replies.1 privateRows
  let run := storedActionRecordedCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness vkTranscriptRepr tapes.1 cache
  (run.1, replies.2 + tapes.2 + run.2 + 3)

/-- The complete stored-bit computation is the original recorded reference experiment on the same raw words. -/
theorem storedActionRecordedBitsCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (budget : ℕ) (bits : Fin ((budget * 22) * 512) → Bool)
    (privateTape : RawPrivateRetryTape inputs.length budget) (cache : ActionRetryOracleState) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let setup := StoredPlonkSetup.encode generators W U
      (plonkKeygenFixedRows actionCircuit) (plonkKeygenSigmaRows actionCircuit)
    let vk := actionReferenceKey (actions := inputs.length) urs rfl actionCircuit_newFixedCols_eq_fifteen
    (storedActionRecordedBitsCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) vkTranscriptRepr budget
      (List.ofFn bits) (List.ofFn (fun i => List.ofFn (privateTape i))) cache).1 =
      actionOracleRecordFromRawTapes urs rfl (fun i : Fin inputs.length => inputs[i.val]) witness vkTranscriptRepr
        (rawMatrixBitsEquiv budget 22 bits) privateTape cache := by
  dsimp only
  unfold storedActionRecordedBitsCosted
  dsimp only
  rewrite [storedRawMatrixCosted_result, zipListCosted_ofFn_result]
  exact storedActionRecordedCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U witness vkTranscriptRepr (rawMatrixBitsEquiv budget 22 bits) privateTape cache

/-- The full counted budget includes decoding and pairing all verifier tapes before executing any retries. -/
def storedActionRecordedBitsCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale actions budget cacheLength bitLength : ℕ)
    (key : StoredPlonkKey) : ℕ :=
  storedRawMatrixCostBudget budget 22 read bitLength +
    storedActionRecordedCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      actions budget cacheLength key + 2 * budget + 4

/-- All real proof, retry, cache, tape-pairing, and bit-decoding costs are discharged internally. -/
theorem storedActionRecordedBitsCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp) (vkTranscriptRepr : Fp)
    (budget : ℕ) (bits : List Bool) (privateRows : List (List (Fin challengeDigestCard)))
    (cache : ActionRetryOracleState) (hprivateLength : privateRows.length = budget)
    (hprivateWidth : ∀ row ∈ privateRows, row.length = fieldSampleCount inputs.length) :
    (storedActionRecordedBitsCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) vkTranscriptRepr budget bits privateRows cache).2 ≤
      storedActionRecordedBitsCostBudget costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
        inputs.length budget cache.length bits.length (StoredPlonkKey.encode vk) := by
  let replies := storedRawMatrixCosted budget 22 read bits
  let tapes := zipListCosted replies.1 privateRows
  have hs := storedRawMatrixCosted_shape budget 22 read bits
  have ht := zipListCosted_shape replies.1 privateRows budget 22 (fieldSampleCount inputs.length)
    hs.1 hprivateLength hs.2 hprivateWidth
  have hp := storedRawMatrixCosted_cost_le budget 22 read bits
  have hz := zipListCosted_cost_le replies.1 privateRows
  have hr := storedActionRecordedCosted_cost_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness vkTranscriptRepr tapes.1 cache ht.2
  rewrite [hs.1] at hz
  rewrite [ht.1] at hr
  unfold storedActionRecordedBitsCosted storedActionRecordedBitsCostBudget
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp hz) hr) 3) (by omega)

end Zcash.Snark.ZeroKnowledge
