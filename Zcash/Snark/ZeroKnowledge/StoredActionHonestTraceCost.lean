import Zcash.Snark.ZeroKnowledge.StoredActionHonestTapeBound
import Zcash.Snark.ZeroKnowledge.StoredActionHonestShape
import Zcash.Snark.ZeroKnowledge.StoredActionTapeTraceCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS omegaOf)
open Zcash.Common
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] plonkReferenceProofFromTape plonkJointViewFromTape
  plonkPublicPolynomialsFromRows rowPolynomial plonkTotalColumnConstructor
  storedPlonkProverTapesCosted plonkChallengesFromTape reduceFieldTape rawBitsTapeEquiv

/-- Produce every original real-prover transcript item from the complete stored bit input. -/
@[irreducible] def storedActionHonestTraceCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (bits : List Bool) : StoredPlonkTraceOutput G × ℕ :=
  let joint := storedActionHonestTapeJointCosted costs node equal read omegaAccess canonicalRead compare
    groupAdd groupScale inputs setup key witness bits
  let access := storedPlonkProverTapeReadBudget inputs.length read
  let trace := storedJointTraceCosted (k := 11) costs equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (joint.1.challenges.x.1, access) (joint.1.challenges.x1.1, access) joint.1.joint
  (⟨joint.1.raw, joint.1.challenges, trace.1⟩, joint.2 + trace.2 + 3)

set_option maxRecDepth 10000 in
/-- Erasing complete transcript production gives the actual reference proof's original schedule. -/
theorem storedActionHonestTraceCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (bits : Fin ((22 + fieldSampleCount inputs.length) * 512) → Bool)
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS G := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    let parts := splitTapeEquiv 22 (fieldSampleCount inputs.length) (Fin challengeDigestCard)
      (rawBitsTapeEquiv (22 + fieldSampleCount inputs.length) bits)
    let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
    (storedActionHonestTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) (List.ofFn bits)).1.trace =
      plonkAttemptTrace (plonkReferenceProofFromTape urs rfl vk pub witness ch (reduceFieldTape parts.2)) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let joint := storedActionHonestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) (List.ofFn bits)
  let parts := splitTapeEquiv 22 (fieldSampleCount inputs.length) (Fin challengeDigestCard)
    (rawBitsTapeEquiv (22 + fieldSampleCount inputs.length) bits)
  let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
  let access := storedPlonkProverTapeReadBudget inputs.length read
  have hj := storedActionHonestTapeJointCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness bits profile homega hn hblind
  have hc : Challenges.eraseCosts joint.1.challenges = ch := by
    unfold joint storedActionHonestTapeJointCosted
    exact storedPlonkProverTapesCosted_challenges_result inputs.length read bits
  have hx : joint.1.challenges.x.1 = ch.x := congrArg (fun c : Challenges 11 Fp => c.x) hc
  have hx1 : joint.1.challenges.x1.1 = ch.x1 := congrArg (fun c : Challenges 11 Fp => c.x1) hc
  have hi : (fun a r => (actionStoredInstanceRowCosted read inputs a r).1) =
      actionInstanceRows (fun action : Fin inputs.length => inputs[action.val]) := by
    funext a r
    exact actionStoredInstanceRowCosted_result read inputs a r
  have hf : (fun c r => (setup.fixedCosted read c r).1) = fixed := by
    funext c r
    exact StoredPlonkSetup.fixedCosted_encode_result generators W U fixed sigma read c r
  have hs : (fun c r => (setup.sigmaCosted read c r).1) = sigma := by
    funext c r
    exact StoredPlonkSetup.sigmaCosted_encode_result generators W U fixed sigma read c r
  unfold storedActionHonestTraceCosted
  change (storedJointTraceCosted (k := 11) costs equal read omegaAccess (actionStoredInstanceRowCosted read inputs)
    (setup.fixedCosted read) (setup.sigmaCosted read) (joint.1.challenges.x.1, access)
    (joint.1.challenges.x1.1, access) joint.1.joint).1 = _
  rewrite [hj, storedJointTraceCosted_result, hi, hf, hs, hx, hx1]
  unfold plonkReferenceProofFromTape plonkVerifierProofFromTape
  rfl

end Zcash.Snark.ZeroKnowledge
