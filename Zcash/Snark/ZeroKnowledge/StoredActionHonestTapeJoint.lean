import Zcash.Snark.ZeroKnowledge.StoredActionHonestJointBound
import Zcash.Snark.ZeroKnowledge.HonestProverPriceBudget
import Zcash.Snark.ZeroKnowledge.StoredActionTapeJointCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS omegaOf)
open Zcash.Common
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] rowPolynomial plonkJointSampleCount
  plonkPublicPolynomialsFromRows plonkTotalColumnConstructor plonkJointViewFromTape
  plonkHonestQuotientPieces storedPlonkProverTapesCosted plonkChallengesFromTape
  reduceFieldTape rawBitsTapeEquiv

/-- Run the complete real Action prover directly on its stored random-bit tape. -/
@[irreducible] def storedActionHonestTapeJointCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (bits : List Bool) : StoredPlonkJointOutput G × ℕ :=
  let tapes := storedPlonkProverTapesCosted inputs.length read bits
  let joint := storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness tapes.1.challenges tapes.1.privateFields
  (⟨tapes.1.raw, tapes.1.challenges, joint.1⟩, tapes.2 + joint.2 + 3)

set_option maxHeartbeats 600000 in
set_option maxRecDepth 10000 in
/-- The complete bit-driven real view is the original joint prover on the same wide-reduced private suffix. -/
theorem storedActionHonestTapeJointCosted_result (costs : FieldOperationCosts)
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
    let construct := plonkTotalColumnConstructor vk pub witness ch
    (storedActionHonestTapeJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) (List.ofFn bits)).1.joint =
      materializePlonkJointView (plonkJointViewFromTape construct [] urs pub
        ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z ch.ipaRound (plonkHonestQuotientPieces vk pub ch)
        (reduceFieldTape parts.2 ∘ Fin.cast (plonkJointSampleCount_eq construct rfl))) := by
  let urs : URS G := { k := 11, g := generators, w := W, u := U }
  let pub := plonkPublicPolynomialsFromRows
    (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
  let produce (ch : Challenges 11 Fp) (tape : Fin (fieldSampleCount inputs.length) → Fp) :=
    let construct := plonkTotalColumnConstructor vk pub witness ch
    materializePlonkJointView (plonkJointViewFromTape construct [] urs pub
      ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z ch.ipaRound (plonkHonestQuotientPieces vk pub ch)
      (tape ∘ Fin.cast (plonkJointSampleCount_eq construct rfl)))
  let parts := splitTapeEquiv 22 (fieldSampleCount inputs.length) (Fin challengeDigestCard)
    (rawBitsTapeEquiv (22 + fieldSampleCount inputs.length) bits)
  let tapes := storedPlonkProverTapesCosted inputs.length read (List.ofFn bits)
  have hch : Challenges.eraseCosts tapes.1.challenges = plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1) :=
    storedPlonkProverTapesCosted_challenges_result inputs.length read bits
  have ht : tapes.1.privateFields = List.ofFn (reduceFieldTape parts.2) :=
    storedPlonkProverTapesCosted_private_result inputs.length read bits
  have h := storedActionHonestJointCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness tapes.1.challenges (reduceFieldTape parts.2) profile homega hn hblind
  change (storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (encodeActionWitness witness)
    tapes.1.challenges (List.ofFn (reduceFieldTape parts.2))).1 = produce (Challenges.eraseCosts tapes.1.challenges)
      (reduceFieldTape parts.2) at h
  rewrite [hch] at h
  unfold storedActionHonestTapeJointCosted
  change (storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
    (encodeActionWitness witness) tapes.1.challenges tapes.1.privateFields).1 = _
  rewrite [ht]
  exact h

end Zcash.Snark.ZeroKnowledge
