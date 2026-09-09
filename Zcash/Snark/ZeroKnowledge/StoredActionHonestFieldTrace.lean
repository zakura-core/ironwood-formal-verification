import Zcash.Snark.ZeroKnowledge.StoredActionHonestJointBound
import Zcash.Snark.ZeroKnowledge.HonestProverDimensions
import Zcash.Snark.ZeroKnowledge.StoredJointTraceSize

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS omegaOf)
variable {G : Type*} [AddCommGroup G] [Module Fp G]
attribute [local irreducible] plonkReferenceProofFromTape plonkJointViewFromTape
  plonkPublicPolynomialsFromRows rowPolynomial plonkTotalColumnConstructor

/-- Construct the original real transcript from a stored private field tape and received challenge readers. -/
@[irreducible] def storedActionHonestFieldTraceCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (ch : Challenges 11 (Fp × ℕ)) (challengeRead : ℕ) (tape : List Fp) :
    List (TranscriptElt Fp G) × ℕ :=
  let joint := storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup key witness ch tape
  let trace := storedJointTraceCosted (k := 11) costs equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (ch.x.1, challengeRead) (ch.x1.1, challengeRead) joint.1
  (trace.1, joint.2 + trace.2 + 2)

set_option maxHeartbeats 600000 in
set_option maxRecDepth 10000 in
/-- The complete stored field computation erases to the original private-tape reference proof. -/
theorem storedActionHonestFieldTraceCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (witness : Fin inputs.length → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges 11 (Fp × ℕ)) (challengeRead : ℕ) (tape : Fin (fieldSampleCount inputs.length) → Fp)
    (profile : PlonkDegreeProfile vk) (homega : vk.omega = omegaOf 11)
    (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5) :
    let urs : URS G := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    (storedActionHonestFieldTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk)
      (encodeActionWitness witness) ch challengeRead (List.ofFn tape)).1 =
      plonkAttemptTrace (plonkReferenceProofFromTape urs rfl vk pub witness (Challenges.eraseCosts ch) tape) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let joint := storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs setup (StoredPlonkKey.encode vk) (encodeActionWitness witness) ch (List.ofFn tape)
  have hj := storedActionHonestJointCosted_result costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
    inputs generators W U fixed sigma vk witness ch tape profile homega hn hblind
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
  unfold storedActionHonestFieldTraceCosted
  change (storedJointTraceCosted (k := 11) costs equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (ch.x.1, challengeRead) (ch.x1.1, challengeRead) joint.1).1 = _
  rewrite [hj, storedJointTraceCosted_result, hi, hf, hs]
  unfold plonkReferenceProofFromTape plonkVerifierProofFromTape
  rfl

/-- Transcript capacity is fixed by the original Action schedule, for all stored values and key data. -/
theorem storedActionHonestFieldTraceCosted_length_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare groupAdd groupScale : ℕ)
    (inputs : List (PublicInputs Fp)) (setup : StoredPlonkSetup G) (key : StoredPlonkKey)
    (witness : List (List (List Fp))) (ch : Challenges 11 (Fp × ℕ)) (challengeRead : ℕ) (tape : List Fp) :
    (storedActionHonestFieldTraceCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness ch challengeRead tape).1.length ≤ 72 * inputs.length + 107 := by
  unfold storedActionHonestFieldTraceCosted
  exact (storedJointTraceCosted_length_le (k := 11) costs equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (ch.x.1, challengeRead) (ch.x1.1, challengeRead)
    (storedActionHonestJointCosted costs node equal read omegaAccess canonicalRead compare groupAdd groupScale
      inputs setup key witness ch tape).1).trans_eq (by omega)

end Zcash.Snark.ZeroKnowledge
