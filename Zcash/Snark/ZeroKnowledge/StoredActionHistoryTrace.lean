import Zcash.Snark.ZeroKnowledge.StoredActionHonestFieldTraceBound
import Zcash.Snark.ZeroKnowledge.StoredHistoryChallengeCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS omegaOf)
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] storedHistoryChallengesCosted plonkReferenceProofFromTape
  plonkPublicPolynomialsFromRows

/-- Recompute the complete original real transcript using precisely the received raw history. -/
@[irreducible] def storedActionHistoryTraceCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (privateFields : List Fp) (history : List (Fin challengeDigestCard)) :
    (Challenges 11 (Fp × ℕ) × List (TranscriptElt Fp G)) × ℕ :=
  let ch := storedHistoryChallengesCosted read history
  let trace := storedActionHonestFieldTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness ch.1 (read + 55) privateFields
  ((ch.1, trace.1), ch.2 + trace.2 + 2)

/-- The generated transcript length is fixed by the original message schedule on every history. -/
theorem storedActionHistoryTraceCosted_length_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (privateFields : List Fp) (history : List (Fin challengeDigestCard)) :
    (storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness privateFields history).1.2.length ≤ 72 * inputs.length + 107 := by
  unfold storedActionHistoryTraceCosted
  exact storedActionHonestFieldTraceCosted_length_le costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness (storedHistoryChallengesCosted read history).1 (read + 55) privateFields

/-- Challenge readers keep the proved constant capacity even as cached replies change their values. -/
theorem storedActionHistoryTraceCosted_readBound (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (privateFields : List Fp) (history : List (Fin challengeDigestCard)) :
    Challenges.ReadBound (storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare
      groupAdd groupScale inputs setup key witness privateFields history).1.1 (read + 55) := by
  unfold storedActionHistoryTraceCosted
  exact storedHistoryChallengesCosted_readBound read history

set_option maxRecDepth 10000 in
/-- Source erasure is the original complete reference proof on the same private tape and raw history. -/
theorem storedActionHistoryTraceCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (privateFields : Fin (fieldSampleCount inputs.length) → Fp) (history : List (Fin challengeDigestCard))
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS G := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    (storedActionHistoryTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) (List.ofFn privateFields) history).1.2 =
      plonkAttemptTrace (plonkReferenceProofFromTape urs rfl vk pub witness
        (plonkChallengesFromDigests 11 (oracleHistoryTape 0 history)) privateFields) := by
  unfold storedActionHistoryTraceCosted
  change (storedActionHonestFieldTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
    (encodeActionWitness witness) (storedHistoryChallengesCosted read history).1 (read + 55) (List.ofFn privateFields)).1 = _
  rewrite [storedActionHonestFieldTraceCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness (storedHistoryChallengesCosted read history).1 (read + 55)
    privateFields profile homega hn hblind]
  rewrite [storedHistoryChallengesCosted_result]
  rfl

end Zcash.Snark.ZeroKnowledge
