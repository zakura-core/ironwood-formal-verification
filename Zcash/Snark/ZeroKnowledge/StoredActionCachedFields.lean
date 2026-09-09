import Zcash.Snark.ZeroKnowledge.StoredActionHistoryOracleBound
import Zcash.Snark.ZeroKnowledge.CachedPrefixSource
import Zcash.Snark.ZeroKnowledge.CachedPrefixBound

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS omegaOf)
attribute [local irreducible] cachedPrefixRunCosted cachedOracleRunTape prefixOracleComp
  plonkReferenceOracleTrace protocolOracleReport protocolQueryAddress

/-- Run the complete real prover online against the supplied cache and stored reply tape. -/
@[irreducible] def storedActionCachedFieldsCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (privateFields : List Fp)
    (initial : List (TranscriptElt Fp VestaG)) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (replies : List (Fin challengeDigestCard)) :
    Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) × ℕ :=
  let run := cachedPrefixRunCosted
    (storedActionHistoryReportCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness privateFields)
    (fun result => (protocolAttemptContinues result, 4))
    (storedActionHistoryQueryCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness privateFields initial)
    (getDListCosted read (0 : Fin challengeDigestCard) replies) 22 [] cache 0
  (some run.1, run.2 + 1)

set_option maxHeartbeats 600000 in
set_option maxRecDepth 10000 in
/-- The counted implementation is exactly the original cached real oracle execution on every supplied tape. -/
theorem storedActionCachedFieldsCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (privateFields : Fin (fieldSampleCount inputs.length) → Fp)
    (initial : List (TranscriptElt Fp VestaG)) (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (replies : Fin 22 → Fin challengeDigestCard)
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    (storedActionCachedFieldsCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) (List.ofFn privateFields) initial cache (List.ofFn replies)).1 =
      cachedOracleRunTape 22 (plonkReferenceOracleComp urs rfl vk pub witness privateFields initial) cache replies := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let pub := plonkPublicPolynomialsFromRows
    (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let produce := plonkReferenceOracleTrace urs rfl vk pub witness privateFields
  let report := storedActionHistoryReportCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) (List.ofFn privateFields)
  let query := storedActionHistoryQueryCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) (List.ofFn privateFields) initial
  let sourceReport := fun raw => protocolOracleReport plonkPointCodec raw
    (plonkAfterChallenge (plonkChallengesFromDigests 11 raw)) (produce raw)
  let sourceQuery := fun raw => protocolQueryAddress initial (produce raw)
  have hr (history : List (Fin challengeDigestCard)) (hl : history.length ≤ 22) (index : ℕ) :
      (report history index).1 = sourceReport (oracleHistoryTape 0 history) index :=
    storedActionHistoryReportCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs generators W U fixed sigma vk witness privateFields history hl index profile homega hn hblind
  have hq (history : List (Fin challengeDigestCard)) (_hl : history.length ≤ 22) (index : ℕ) :
      (query history index).1 = sourceQuery (oracleHistoryTape 0 history) index :=
    storedActionHistoryQueryCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs generators W U fixed sigma vk witness privateFields initial history index profile homega hn hblind
  have h := cachedPrefixRunCosted_result_of_history_bound (0 : Fin challengeDigestCard)
    sourceReport protocolAttemptContinues sourceQuery report (fun result => (protocolAttemptContinues result, 4))
    query (getDListCosted read (0 : Fin challengeDigestCard) (List.ofFn replies)) 22 hr (fun _ => rfl) hq
    22 [] cache 0 (by decide)
  have hreply : (fun index : Fin 22 =>
      (getDListCosted read (0 : Fin challengeDigestCard) (List.ofFn replies) index.val).1) = replies := by
    funext index
    exact getDListCosted_ofFn_result read (0 : Fin challengeDigestCard) replies index
  simp only [Nat.zero_add] at h
  rewrite [hreply] at h
  unfold storedActionCachedFieldsCosted plonkReferenceOracleComp protocolOracleComp
  exact h

end Zcash.Snark.ZeroKnowledge
