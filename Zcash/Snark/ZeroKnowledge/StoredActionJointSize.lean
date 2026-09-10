import Zcash.Snark.ZeroKnowledge.StoredActionTapeJointCost
import Zcash.Snark.ZeroKnowledge.JointViewSize

/-! # Concrete output dimensions of the bit-driven Action joint simulator -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common
variable {G : Type*} [AddCommGroup G] [Module Fp G]

set_option maxRecDepth 10000 in
/-- Every complete input bit tape produces the original commitment, observation, and round dimensions. -/
theorem storedActionTapeJointCosted_shape
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G)
    (bits : Fin ((22 + plonkSimulatorSampleCount inputs.length 11) * 512) → Bool) :
    let stored := (storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (List.ofFn bits)).1.joint
    stored.1.1.length = 22 * inputs.length + 10 ∧
      stored.1.2.1.length = 22 * inputs.length ∧
      (∀ row ∈ stored.1.2.1, row.length = 5) ∧ stored.2.messages.length = 11 := by
  let urs : URS G := { k := 11, g := generators, w := W, u := U }
  let pub := plonkPublicPolynomialsFromRows
    (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
  let parts := splitTapeEquiv 22 (plonkSimulatorSampleCount inputs.length 11) (Fin challengeDigestCard)
    (rawBitsTapeEquiv (22 + plonkSimulatorSampleCount inputs.length 11) bits)
  let ch := plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1)
  let coins := plonkSimulatorTapeEquiv inputs.length 11 (reduceFieldTape parts.2)
  let original := plonkJointSimulatorFromCoins urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3
    ch.xi ch.z ch.ipaRound (plonkVerifierHx vk pub ch) coins.1 coins.2.1.1 coins.2.2 coins.2.1.2
  let output := storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs
    (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (List.ofFn bits)
  have hout : output.1.joint = materializePlonkJointView original :=
    storedActionTapeJointCosted_result fieldCosts ipaCosts node equal read omegaAccess
      inputs generators W U fixed sigma vk bits
  have hshape := materializePlonkJointView_shape original
  have hcolumns : original.1.2.1.length = 22 * inputs.length := by
    simp only [original, plonkJointSimulatorFromCoins, plonkMaskSimulatorFromCoins, List.length_ofFn]
  change output.1.joint.1.1.length = _ ∧ output.1.joint.1.2.1.length = _ ∧
    (∀ row ∈ output.1.joint.1.2.1, row.length = 5) ∧ output.1.joint.2.messages.length = 11
  rw [hout]
  exact ⟨hshape.1, hshape.2.1.trans hcolumns, hshape.2.2.1, hshape.2.2.2⟩

end Zcash.Snark.ZeroKnowledge
