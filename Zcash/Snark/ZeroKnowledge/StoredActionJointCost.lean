import Zcash.Snark.ZeroKnowledge.PlonkJointSimulatorCostBound
import Zcash.Snark.ZeroKnowledge.StoredPlonkSetupCost
import Zcash.Snark.ZeroKnowledge.ActionPublicInputCost

/-!
# Joint simulation on stored Action inputs and setup

This adapter supplies the actual ten-field Action instance layout and concrete
stored setup readers to the complete algebraic simulator. Its representation
theorem retains every original public input and finite setup entry. No polynomial
or generator reader is an arbitrary unpriced host callback.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Run the full algebraic simulator using materialized Action input and setup data. -/
def storedActionJointSimulatorCosted (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess : ℕ) (inputs : List (PublicInputs Fp))
    (setup : StoredPlonkSetup G) (key : StoredPlonkKey) (ch : Challenges 11 (Fp × ℕ))
    (blinds : Fin (22 * inputs.length + 10) → Fp × ℕ)
    (observations : Fin (22 * inputs.length) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ)
    (roundCoins : Fin 11 → (Fp × Fp) × ℕ) (scalarCoin finalBlind : Fp × ℕ) :
    ((List G × (List (List Fp) × (Fp × Fp))) × MaterializedIpaTranscript Fp G) × ℕ :=
  plonkJointSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (setup.generatorCosted read) (setup.w, read + 1) (setup.u, read + 1) key ch
    blinds observations linear firstGroup roundCoins scalarCoin finalBlind

set_option maxRecDepth 10000 in
/-- The stored adapter recovers the original Action rows, supplied setup, and entire joint simulation. -/
theorem storedActionJointSimulatorCosted_result
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (vk : VerifyingKey (plonkProofShape inputs.length 11) Fp G) (ch : Challenges 11 (Fp × ℕ))
    (blinds : Fin (22 * inputs.length + 10) → Fp × ℕ)
    (observations : Fin (22 * inputs.length) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ)
    (roundCoins : Fin 11 → (Fp × Fp) × ℕ) (scalarCoin finalBlind : Fp × ℕ) :
    let urs : URS G := { k := 11, g := generators, w := W, u := U }
    let pub := plonkPublicPolynomialsFromRows
      (actionInstanceRows (fun action : Fin inputs.length => inputs[action.val])) fixed sigma
    (storedActionJointSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) (StoredPlonkKey.encode vk) ch
      blinds observations linear firstGroup roundCoins scalarCoin finalBlind).1 =
      materializePlonkJointView (plonkJointSimulatorFromCoins urs pub ch.x.1 ch.x1.1 ch.x2.1 ch.x4.1 ch.x3.1
        ch.xi.1 ch.z.1 (fun index => (ch.ipaRound index).1) (plonkVerifierHx vk pub (Challenges.eraseCosts ch))
        (fun index => (blinds index).1, fun column index => (observations column index).1, linear.1, firstGroup.1)
        (fun index => (roundCoins index).1) scalarCoin.1 finalBlind.1) := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
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
  have hgenerators : (fun index : Fin (2 ^ 11) => (setup.generatorCosted read index).1) = generators := by
    funext index
    exact StoredPlonkSetup.generatorCosted_encode_result generators W U fixed sigma read index
  have h := plonkJointSimulatorCosted_result fieldCosts ipaCosts node equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (setup.generatorCosted read) (W, read + 1) (U, read + 1) vk ch blinds observations
    linear firstGroup roundCoins scalarCoin finalBlind
  dsimp only at h ⊢
  change (storedActionJointSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs
    setup (StoredPlonkKey.encode vk) ch blinds observations linear firstGroup roundCoins scalarCoin finalBlind).1 = _ at h
  rw [hrows, hfixed, hsigma, hgenerators] at h
  exact h

/-- A concrete common access bound from the Action count, coin reads, and fixed setup dimensions. -/
def storedActionJointInputBudget (actions coinRead read : ℕ) : ℕ :=
  25 * actions + coinRead + 2 * read + 4200

end Zcash.Snark.ZeroKnowledge
