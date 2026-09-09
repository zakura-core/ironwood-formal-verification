import Zcash.Snark.ZeroKnowledge.StoredActionHonestTraceBound
import Zcash.Snark.ZeroKnowledge.CanonicalOracleViewCost
import Zcash.Snark.ZeroKnowledge.StoredProverDigestCost
import Zcash.Snark.ZeroKnowledge.PlonkOracle

/-!
# Complete real Action oracle-view production from stored random bits

This stage includes the entire tape-to-proof computation, canonical reports,
encoded query addresses, public raw replies, and the original stopping replay.
Its supplied public initialization is constructed by the following composition
stage. Private suffix words remain internal to this computation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common
attribute [local irreducible] storedPlonkProverTapesCosted plonkChallengesFromTape
  reduceFieldTape rawBitsTapeEquiv plonkPublicPolynomialsFromRows plonkReferenceProofFromTape
  canonicalProtocolOracleViewCosted protocolOracleView plonkAttemptTrace

/-- Produce the complete original proof attempt and its exact raw query/reply prefix. -/
def storedActionHonestOracleViewCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey) (witness : List (List (List Fp))) (bits : List Bool)
    (initial : List (TranscriptElt Fp VestaG)) :
    (ProverAttemptResult × List (TranscriptHashAddress × Fin challengeDigestCard)) × ℕ :=
  let produced := storedActionHonestTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs setup key witness bits
  let observed := canonicalProtocolOracleViewCosted equal read initial produced.1.challenges
    (storedDigestPrefixCosted 22 read produced.1.raw) produced.1.trace
  (observed.1, produced.2 + observed.2 + 3)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- Every stored bit tape gives exactly the original real prover's raw oracle view, including failures. -/
theorem storedActionHonestOracleViewCosted_result
    (costs : FieldOperationCosts) (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (bits : Fin ((22 + fieldSampleCount inputs.length) * 512) → Bool)
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = Zcash.Arithmetic.omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (initial : List (TranscriptElt Fp VestaG)) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    let parts := splitTapeEquiv 22 (fieldSampleCount inputs.length) (Fin challengeDigestCard)
      (rawBitsTapeEquiv (22 + fieldSampleCount inputs.length) bits)
    let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
    (storedActionHonestOracleViewCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (encodeActionWitness witness) (List.ofFn bits) initial).1 =
      plonkRawOracleView initial parts.1 (plonkReferenceProofFromTape urs rfl vk pub witness ch (reduceFieldTape parts.2)) := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let pub := plonkPublicPolynomialsFromRows
    (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let produced := storedActionHonestTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale inputs
    setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) (List.ofFn bits)
  let parts := splitTapeEquiv 22 (fieldSampleCount inputs.length) (Fin challengeDigestCard)
    (rawBitsTapeEquiv (22 + fieldSampleCount inputs.length) bits)
  let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
  have hsource : produced.1.raw = (storedPlonkProverTapesCosted inputs.length read (List.ofFn bits)).1.raw ∧
      produced.1.challenges = (storedPlonkProverTapesCosted inputs.length read (List.ofFn bits)).1.challenges := by
    unfold produced storedActionHonestTraceCosted storedActionHonestTapeJointCosted
    exact ⟨rfl, rfl⟩
  have hch : Challenges.eraseCosts produced.1.challenges = ch := by
    rewrite [hsource.2]
    exact storedPlonkProverTapesCosted_challenges_result inputs.length read bits
  have hraw : (fun index => (storedDigestPrefixCosted 22 read produced.1.raw index).1) =
      extendDigestTape parts.1 := by
    funext index
    rewrite [hsource.1]
    exact storedPlonkProverTapesCosted_digest_result inputs.length read bits index
  have hagree (index : ℕ) :
      (((storedDigestPrefixCosted 22 read produced.1.raw index).1).val : Fp) =
        plonkAttemptChallenge (Challenges.eraseCosts produced.1.challenges) index := by
    rewrite [hsource.1, hsource.2]
    exact storedPlonkProverTapesCosted_digest_agreement inputs.length read bits index
  have htrace : produced.1.trace =
      plonkAttemptTrace (plonkReferenceProofFromTape urs rfl vk pub witness ch (reduceFieldTape parts.2)) :=
    storedActionHonestTraceCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs generators W U fixed sigma vk witness bits profile homega hn hblind
  have h := canonicalProtocolOracleViewCosted_result equal read initial produced.1.challenges
    (storedDigestPrefixCosted 22 read produced.1.raw) hagree produced.1.trace
  conv at h =>
    rhs
    rw [hraw, hch, htrace]
  change (canonicalProtocolOracleViewCosted equal read initial produced.1.challenges
    (storedDigestPrefixCosted 22 read produced.1.raw) produced.1.trace).1 = _
  have hcast : plonkChallengesFromTape (k := 11) (fun index => ((parts.1 index).val : Fp)) = ch := by
    apply congrArg (plonkChallengesFromTape (k := 11))
    funext index
    unfold reduceFieldTape
    rfl
  unfold plonkRawOracleView
  rewrite [plonkChallengesFromDigests_extend]
  rewrite [hcast]
  exact h

end Zcash.Snark.ZeroKnowledge
