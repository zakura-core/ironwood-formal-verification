import Zcash.Snark.ZeroKnowledge.StoredActionHistoryTraceBound
import Zcash.Snark.ZeroKnowledge.CanonicalOracleReportCost
import Zcash.Snark.ZeroKnowledge.QueryAddressCost
import Zcash.Snark.ZeroKnowledge.PlonkOracle

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS omegaOf)
attribute [local irreducible] plonkReferenceProofFromTape plonkPublicPolynomialsFromRows
  storedHistoryChallengesCosted canonicalProtocolOracleReportCosted protocolOracleReport

/-- Recompute the original due report, including the entire real prover, encoding, and stopping checks. -/
@[irreducible] def storedActionHistoryReportCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (privateFields : List Fp)
    (history : List (Fin challengeDigestCard)) (index : ℕ) : ProverAttemptResult × ℕ :=
  let produced := storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness privateFields history
  let observed := canonicalProtocolOracleReportCosted equal read produced.1.1 produced.1.2 index
  (observed.1, produced.2 + observed.2 + 2)

/-- Recompute the exact personalized byte query from the same received-history reference computation. -/
@[irreducible] def storedActionHistoryQueryCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (privateFields : List Fp)
    (initial : List (TranscriptElt Fp VestaG)) (history : List (Fin challengeDigestCard)) (index : ℕ) :
    TranscriptHashAddress × ℕ :=
  let produced := storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness privateFields history
  let query := protocolQueryAddressCosted read initial produced.1.2 index
  (query.1, produced.2 + query.2 + 2)

set_option maxHeartbeats 600000 in
set_option maxRecDepth 10000 in
/-- Every reachable report preserves the original cached-oracle prefix and failure status. -/
theorem storedActionHistoryReportCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (privateFields : Fin (fieldSampleCount inputs.length) → Fp) (history : List (Fin challengeDigestCard))
    (hlength : history.length ≤ 22) (index : ℕ)
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    (storedActionHistoryReportCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) (List.ofFn privateFields) history index).1 =
      protocolOracleReport plonkPointCodec (oracleHistoryTape 0 history)
        (plonkAfterChallenge (plonkChallengesFromDigests 11 (oracleHistoryTape 0 history)))
        (plonkReferenceOracleTrace urs rfl vk pub witness privateFields (oracleHistoryTape 0 history)) index := by
  let produced := storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
    (encodeActionWitness witness) (List.ofFn privateFields) history
  have hch : Challenges.eraseCosts produced.1.1 = plonkChallengesFromDigests 11 (oracleHistoryTape 0 history) := by
    unfold produced storedActionHistoryTraceCosted
    exact storedHistoryChallengesCosted_result read history
  have hraw (i : ℕ) : ((oracleHistoryTape 0 history i).val : Fp) =
      plonkAttemptChallenge (Challenges.eraseCosts produced.1.1) i := by
    unfold produced storedActionHistoryTraceCosted
    exact storedHistoryChallengesCosted_agreement read history hlength i
  have htrace := storedActionHistoryTraceCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness privateFields history profile homega hn hblind
  have h := canonicalProtocolOracleReportCosted_result equal read produced.1.1 (oracleHistoryTape 0 history)
    hraw produced.1.2 index
  conv at h => rhs; rewrite [hch, htrace]
  unfold storedActionHistoryReportCosted plonkReferenceOracleTrace
  exact h

set_option maxRecDepth 10000 in
/-- Every encoded online query is exactly the address requested by the original reference oracle program. -/
theorem storedActionHistoryQueryCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (privateFields : Fin (fieldSampleCount inputs.length) → Fp)
    (initial : List (TranscriptElt Fp VestaG)) (history : List (Fin challengeDigestCard)) (index : ℕ)
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    (storedActionHistoryQueryCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) (List.ofFn privateFields) initial history index).1 =
      protocolQueryAddress initial
        (plonkReferenceOracleTrace urs rfl vk pub witness privateFields (oracleHistoryTape 0 history)) index := by
  have htrace := storedActionHistoryTraceCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness privateFields history profile homega hn hblind
  unfold storedActionHistoryQueryCosted plonkReferenceOracleTrace
  rewrite [protocolQueryAddressCosted_result, htrace]
  rfl

end Zcash.Snark.ZeroKnowledge
