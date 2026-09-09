import Zcash.Snark.ZeroKnowledge.StoredActionTapeJointCost
import Zcash.Snark.ZeroKnowledge.PlonkJointPriceBudget

/-!
# The bit-driven joint simulator's complete cost bound

Every challenge and private-coin access premise is discharged by the tape
producer. Public row and setup accesses are already supplied by the stored Action
adapter. The bound adds the complete tape production and algebraic computation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The complete bit-driven algebraic runtime bound has no unproved reader-price premises. -/
theorem storedActionTapeJointCosted_cost_le
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (key : StoredPlonkKey) (bits : List Bool) :
    (storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) key bits).2 ≤
      plonkStoredTapeCostBudget inputs.length 11 read bits.length +
        plonkJointSimulatorCostBudget fieldCosts ipaCosts node equal read omegaAccess inputs.length
          (storedActionJointInputBudget inputs.length (plonkStoredTapeReadBudget inputs.length 11 read) read)
          (read + 1) key (storedPlonkSimulatorTapesCosted inputs.length 11 read bits).1.challenges + 3 := by
  let tapes := storedPlonkSimulatorTapesCosted inputs.length 11 read bits
  let coins := tapes.1.coins
  have hreaders := storedPlonkSimulatorTapesCosted_readBound inputs.length 11 read bits
  rcases hreaders.2 with ⟨hblinds, hobs, hlinear, hfirst, hrounds, hscalar, hblind⟩
  have hjoint := storedActionJointSimulatorCosted_cost_le fieldCosts ipaCosts node equal read omegaAccess
    inputs generators W U fixed sigma key tapes.1.challenges coins.blinds coins.observations
    coins.linear coins.firstGroup coins.roundCoins coins.scalarCoin coins.finalBlind
    (plonkStoredTapeReadBudget inputs.length 11 read) hreaders.1 hblinds hobs hlinear hfirst hrounds hscalar hblind
  have htape := storedPlonkSimulatorTapesCosted_cost_le inputs.length 11 read bits
  exact Nat.add_le_add_right (Nat.add_le_add htape hjoint) 3

/-- The eleven-round common input-access envelope is linear in Action count and primitive read price. -/
theorem storedActionTapeJointInputBudget_eleven (actions read : ℕ) :
    storedActionJointInputBudget actions (plonkStoredTapeReadBudget actions 11 read) read =
      553 * actions + 4 * read + 4457 := by
  simp only [storedActionJointInputBudget, plonkStoredTapeReadBudget, plonkSimulatorSampleCount_eleven]
  omega

/-- A complete algebraic runtime envelope independent of every sampled bit and field value. -/
def storedActionTapeJointCostBudget (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts)
    (node equal read omegaAccess actions bitLength : ℕ) (key : StoredPlonkKey) : ℕ :=
  plonkStoredTapeCostBudget actions 11 read bitLength +
    plonkJointSimulatorCostBudget fieldCosts ipaCosts node equal read omegaAccess actions
      (storedActionJointInputBudget actions (plonkStoredTapeReadBudget actions 11 read) read)
      (read + 1) key (storedPlonkChallengePriceModel 11 read) + 3

/-- Every possible bit tape satisfies the same explicit input-size and primitive-cost envelope. -/
theorem storedActionTapeJointCosted_cost_le_fixed
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (key : StoredPlonkKey) (bits : List Bool) :
    (storedActionTapeJointCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) key bits).2 ≤
      storedActionTapeJointCostBudget fieldCosts ipaCosts node equal read omegaAccess inputs.length bits.length key := by
  have h := storedActionTapeJointCosted_cost_le fieldCosts ipaCosts node equal read omegaAccess
    inputs generators W U fixed sigma key bits
  have hbudget := plonkJointSimulatorCostBudget_congr_prices fieldCosts ipaCosts node equal read omegaAccess
    inputs.length (storedActionJointInputBudget inputs.length (plonkStoredTapeReadBudget inputs.length 11 read) read)
    (read + 1) key (storedPlonkSimulatorTapesCosted inputs.length 11 read bits).1.challenges
    (storedPlonkChallengePriceModel 11 read)
    (storedPlonkSimulatorTapesCosted_challenge_prices inputs.length 11 read bits)
  exact h.trans_eq (congrArg (fun budget => plonkStoredTapeCostBudget inputs.length 11 read bits.length + budget + 3) hbudget)

end Zcash.Snark.ZeroKnowledge
