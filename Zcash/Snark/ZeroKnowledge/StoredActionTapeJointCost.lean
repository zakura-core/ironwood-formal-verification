import Zcash.Snark.ZeroKnowledge.StoredActionJointCostBound
import Zcash.Snark.ZeroKnowledge.PlonkStoredTapeBound

/-!
# The complete algebraic Action simulator from stored bits

This composition pays for the bit-tape producer and supplies its actual readers
to the complete PLONK and IPA computation. Raw replies and prepared challenges
remain available for the later proof encoding and oracle observation stages.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
open Zcash.Common
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Fully produced algebraic output and the original raw reply and challenge state. -/
structure StoredPlonkJointOutput (G : Type*) where
  raw : List (Fin challengeDigestCard)
  challenges : Challenges 11 (Fp × ℕ)
  joint : (List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G

/-- Compute the complete stored Action joint view directly from its materialized bit tape. -/
def storedActionTapeJointCosted (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup G) (key : StoredPlonkKey) (bits : List Bool) :
    StoredPlonkJointOutput G × ℕ :=
  let tapes := storedPlonkSimulatorTapesCosted inputs.length 11 read bits
  let coins := tapes.1.coins
  let joint := storedActionJointSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs
    setup key tapes.1.challenges coins.blinds coins.observations coins.linear coins.firstGroup
    coins.roundCoins coins.scalarCoin coins.finalBlind
  ({ raw := tapes.1.raw, challenges := tapes.1.challenges, joint := joint.1 }, tapes.2 + joint.2 + 3)

/-- The raw reply state is exactly the original tape producer's output. -/
theorem storedActionTapeJointCosted_raw (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup G) (key : StoredPlonkKey) (bits : List Bool) :
    (storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup key bits).1.raw =
      (storedPlonkSimulatorTapesCosted inputs.length 11 read bits).1.raw := rfl

/-- The challenge state retains every prepared challenge and its complete access price. -/
theorem storedActionTapeJointCosted_challenges
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup G) (key : StoredPlonkKey) (bits : List Bool) :
    (storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs setup key bits).1.challenges =
      (storedPlonkSimulatorTapesCosted inputs.length 11 read bits).1.challenges := rfl

set_option maxRecDepth 10000 in
/-- The bit-driven joint output is exactly the original simulator on the original split tape. -/
theorem storedActionTapeJointCosted_result
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
    let coins := plonkSimulatorTapeEquiv inputs.length 11 (reduceFieldTape parts.2)
    (storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) (List.ofFn bits)).1.joint =
      materializePlonkJointView (plonkJointSimulatorFromCoins urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3
        ch.xi ch.z ch.ipaRound (plonkVerifierHx vk pub ch) coins.1 coins.2.1.1 coins.2.2 coins.2.1.2) := by
  let urs : URS G := { k := 11, g := generators, w := W, u := U }
  let pub := plonkPublicPolynomialsFromRows
    (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
  let tapes := storedPlonkSimulatorTapesCosted inputs.length 11 read (List.ofFn bits)
  let coins := tapes.1.coins
  let ch := tapes.1.challenges
  let simulate (ch : Challenges 11 Fp)
      (coins : PlonkMaskSimulatorCoins inputs.length × (((Fin 11 → Fp × Fp) × Fp) × Fp)) :=
    materializePlonkJointView (plonkJointSimulatorFromCoins urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3
      ch.xi ch.z ch.ipaRound (plonkVerifierHx vk pub ch) coins.1 coins.2.1.1 coins.2.2 coins.2.1.2)
  have hencode (preparedChallenges : Challenges 11 (Fp × ℕ))
      (preparedCoins : PlonkSimulatorCoinsCosted inputs.length 11) :
      (storedActionJointSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs
        (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) preparedChallenges
        preparedCoins.blinds preparedCoins.observations preparedCoins.linear preparedCoins.firstGroup
        preparedCoins.roundCoins preparedCoins.scalarCoin preparedCoins.finalBlind).1 =
        simulate (Challenges.eraseCosts preparedChallenges) preparedCoins.erase := by
    exact storedActionJointSimulatorCosted_result fieldCosts ipaCosts node equal read omegaAccess
      inputs generators W U fixed sigma vk preparedChallenges preparedCoins.blinds preparedCoins.observations
      preparedCoins.linear preparedCoins.firstGroup preparedCoins.roundCoins preparedCoins.scalarCoin preparedCoins.finalBlind
  have hch := storedPlonkSimulatorTapesCosted_challenges_result inputs.length 11 read bits
  have hcoins := storedPlonkSimulatorTapesCosted_coins_result inputs.length 11 read bits
  change Challenges.eraseCosts ch = _ at hch
  change coins.erase = _ at hcoins
  exact (hencode ch coins).trans (congrArg₂ simulate hch hcoins)

end Zcash.Snark.ZeroKnowledge
