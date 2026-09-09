import Zcash.Snark.ZeroKnowledge.StoredActionTapeTraceBound
import Zcash.Snark.ZeroKnowledge.CanonicalOracleViewCost
import Zcash.Snark.ZeroKnowledge.StoredDigestPrefixCost
import Zcash.Snark.ZeroKnowledge.PlonkOracle

/-!
# Complete Action oracle-view production from stored random bits

This stage includes the entire tape-to-proof computation, canonical reports,
encoded query addresses, public raw replies, and the original stopping replay.
Its supplied public initialization is constructed by the following composition
stage. Private suffix words remain internal to this computation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common

/-- Produce the complete original proof attempt and its exact raw query/reply prefix. -/
def storedActionOracleViewCosted (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup VestaG) (key : StoredPlonkKey) (bits : List Bool)
    (initial : List (TranscriptElt Fp VestaG)) :
    (ProverAttemptResult × List (TranscriptHashAddress × Fin challengeDigestCard)) × ℕ :=
  let produced := storedActionTapeTraceCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup key bits
  let observed := canonicalProtocolOracleViewCosted equal read initial produced.1.challenges
    (storedDigestPrefixCosted 22 read produced.1.raw) produced.1.trace
  (observed.1, produced.2 + observed.2 + 3)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- Every stored bit tape gives exactly the original simulator's raw oracle view, including failures. -/
theorem storedActionOracleViewCosted_result
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → VestaG) (W U : VestaG)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp VestaG)
    (bits : Fin ((22 + plonkSimulatorSampleCount inputs.length 11) * 512) → Bool)
    (initial : List (TranscriptElt Fp VestaG)) :
    let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    let parts := splitTapeEquiv 22 (plonkSimulatorSampleCount inputs.length 11) (Fin challengeDigestCard)
      (rawBitsTapeEquiv (22 + plonkSimulatorSampleCount inputs.length 11) bits)
    let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
    (storedActionOracleViewCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (List.ofFn bits) initial).1 =
      plonkRawOracleView initial parts.1 (plonkVerifierSimulatorFromTape urs vk pub ch (reduceFieldTape parts.2)) := by
  let urs : URS VestaG := { k := 11, g := generators, w := W, u := U }
  let pub := plonkPublicPolynomialsFromRows
    (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let produced := storedActionTapeTraceCosted fieldCosts ipaCosts node equal read omegaAccess inputs
    setup (StoredPlonkKey.encode vk) (List.ofFn bits)
  let parts := splitTapeEquiv 22 (plonkSimulatorSampleCount inputs.length 11) (Fin challengeDigestCard)
    (rawBitsTapeEquiv (22 + plonkSimulatorSampleCount inputs.length 11) bits)
  let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
  have hch : Challenges.eraseCosts produced.1.challenges = ch :=
    storedPlonkSimulatorTapesCosted_challenges_result inputs.length 11 read bits
  have hraw : (fun index => (storedDigestPrefixCosted 22 read produced.1.raw index).1) =
      extendDigestTape parts.1 := by
    funext index
    exact storedPlonkSimulatorTapesCosted_digest_result inputs.length 11 read bits index
  have hagree (index : ℕ) :
      (((storedDigestPrefixCosted 22 read produced.1.raw index).1).val : Fp) =
        plonkAttemptChallenge (Challenges.eraseCosts produced.1.challenges) index :=
    storedPlonkSimulatorTapesCosted_digest_agreement inputs.length 11 read bits index
  have htrace : produced.1.trace =
      plonkAttemptTrace (plonkVerifierSimulatorFromTape urs vk pub ch (reduceFieldTape parts.2)) :=
    storedActionTapeTraceCosted_result fieldCosts ipaCosts node equal read omegaAccess
      inputs generators W U fixed sigma vk bits
  have h := canonicalProtocolOracleViewCosted_result equal read initial produced.1.challenges
    (storedDigestPrefixCosted 22 read produced.1.raw) hagree produced.1.trace
  conv at h =>
    rhs
    rw [hraw, hch, htrace]
  change (canonicalProtocolOracleViewCosted equal read initial produced.1.challenges
    (storedDigestPrefixCosted 22 read produced.1.raw) produced.1.trace).1 = _
  simpa only [plonkRawOracleView, plonkChallengesFromDigests_extend] using h

end Zcash.Snark.ZeroKnowledge
