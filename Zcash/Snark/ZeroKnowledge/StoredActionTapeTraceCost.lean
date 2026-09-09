import Zcash.Snark.ZeroKnowledge.StoredActionTapeJointBound
import Zcash.Snark.ZeroKnowledge.StoredJointTraceCost

/-!
# The complete Action transcript from stored random bits

The complete tape and joint producers feed the actual priced proof constructor.
The two reused evaluation challenges are charged at their proved tape-reader
envelope. Every output field is forced into the original transcript before the
later canonical observer can stop on an exceptional value.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Internal transcript-production state, retaining raw replies and the prepared challenges. -/
structure StoredPlonkTraceOutput (G : Type*) where
  raw : List (Fin challengeDigestCard)
  challenges : Challenges 11 (Fp × ℕ)
  trace : List (TranscriptElt Fp G)

/-- Produce the complete original Action message schedule from a stored bit tape. -/
def storedActionTapeTraceCosted (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup G) (key : StoredPlonkKey) (bits : List Bool) :
    StoredPlonkTraceOutput G × ℕ :=
  let joint := storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup key bits
  let access := plonkStoredTapeReadBudget inputs.length 11 read
  let trace := storedJointTraceCosted (k := 11) fieldCosts equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint
  ({ raw := joint.1.raw, challenges := joint.1.challenges, trace := trace.1 }, joint.2 + trace.2 + 3)

/-- Repricing the two reused challenges retains a proved upper bound on their original complete readers. -/
theorem storedActionTapeTraceCosted_challenge_repricing
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup G) (key : StoredPlonkKey) (bits : List Bool) :
    let ch := (storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup key bits).1.challenges
    ch.x.2 ≤ plonkStoredTapeReadBudget inputs.length 11 read ∧
      ch.x1.2 ≤ plonkStoredTapeReadBudget inputs.length 11 read := by
  have h := (storedPlonkSimulatorTapesCosted_readBound inputs.length 11 read bits).1
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- The bit-driven transcript is exactly the original flat-tape simulator's complete schedule. -/
theorem storedActionTapeTraceCosted_result
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (bits : Fin ((22 + plonkSimulatorSampleCount inputs.length 11) * 512) → Bool) :
    let urs : URS G := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    let parts := splitTapeEquiv 22 (plonkSimulatorSampleCount inputs.length 11) (Fin challengeDigestCard)
      (rawBitsTapeEquiv (22 + plonkSimulatorSampleCount inputs.length 11) bits)
    let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
    (storedActionTapeTraceCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (List.ofFn bits)).1.trace =
      plonkAttemptTrace (plonkVerifierSimulatorFromTape urs vk pub ch (reduceFieldTape parts.2)) := by
  let urs : URS G := { k := 11, g := generators, w := W, u := U }
  let pub := plonkPublicPolynomialsFromRows
    (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let joint := storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs
    setup (StoredPlonkKey.encode vk) (List.ofFn bits)
  let access := plonkStoredTapeReadBudget inputs.length 11 read
  let parts := splitTapeEquiv 22 (plonkSimulatorSampleCount inputs.length 11) (Fin challengeDigestCard)
    (rawBitsTapeEquiv (22 + plonkSimulatorSampleCount inputs.length 11) bits)
  let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
  let coins := plonkSimulatorTapeEquiv inputs.length 11 (reduceFieldTape parts.2)
  let original := plonkJointSimulatorFromCoins urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3
    ch.xi ch.z ch.ipaRound (plonkVerifierHx vk pub ch) coins.1 coins.2.1.1 coins.2.2 coins.2.1.2
  have hrows : (fun action row => (actionStoredInstanceRowCosted read inputs action row).1) =
      actionInstanceRows (fun action : Fin inputs.length => inputs[action.val]) := by
    funext action row
    exact actionStoredInstanceRowCosted_result read inputs action row
  have hfixed : (fun column row => (setup.fixedCosted read column row).1) = fixed := by
    funext column row
    exact StoredPlonkSetup.fixedCosted_encode_result generators W U fixed sigma read column row
  have hsigma : (fun column row => (setup.sigmaCosted read column row).1) = sigma := by
    funext column row
    exact StoredPlonkSetup.sigmaCosted_encode_result generators W U fixed sigma read column row
  let observe (prepared : Challenges 11 Fp)
      (view : PreIpaMaskView 5 (22 * inputs.length + 10) G × IpaTranscript 11 Fp G) :=
    plonkAttemptTrace (plonkProofFromJointView pub prepared.x prepared.x1 view)
  have hroute (prepared : Challenges 11 (Fp × ℕ))
      (view : PreIpaMaskView 5 (22 * inputs.length + 10) G × IpaTranscript 11 Fp G) :
      (storedJointTraceCosted (k := 11) fieldCosts equal read omegaAccess
        (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
        (prepared.x.1, access) (prepared.x1.1, access) (materializePlonkJointView view)).1 =
        observe (Challenges.eraseCosts prepared) view := by
    have h := storedJointTraceCosted_result fieldCosts equal read omegaAccess
      (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
      (prepared.x.1, access) (prepared.x1.1, access) view
    rw [hrows, hfixed, hsigma] at h
    exact h
  have hjoint : joint.1.joint = materializePlonkJointView original :=
    storedActionTapeJointCosted_result fieldCosts ipaCosts node equal read omegaAccess
      inputs generators W U fixed sigma vk bits
  have hch : Challenges.eraseCosts joint.1.challenges = ch :=
    storedPlonkSimulatorTapesCosted_challenges_result inputs.length 11 read bits
  change (storedJointTraceCosted (k := 11) fieldCosts equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint).1 = _
  rw [hjoint]
  have h := hroute joint.1.challenges original
  rw [hch] at h
  exact h

end Zcash.Snark.ZeroKnowledge
