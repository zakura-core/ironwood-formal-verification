import Zcash.Snark.ZeroKnowledge.StoredActionJointCost

/-!
# Concrete Action-input bounds for complete algebraic simulation

The public-row, setup, and generator access premises of the joint theorem are
all discharged from their stored representations. Remaining read premises concern
only the challenge and private-coin producers that the bit-tape stage supplies.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The complete joint bound is instantiated by actual stored Action inputs and setup dimensions. -/
theorem storedActionJointSimulatorCosted_cost_le
    (fieldCosts : FieldOperationCosts) (ipaCosts : IpaOperationCosts) (node equal read omegaAccess : ℕ)
    (inputs : List (PublicInputs Fp)) (generators : Fin 2048 → G) (W U : G)
    (fixed : Fin 29 → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (key : StoredPlonkKey) (ch : Challenges 11 (Fp × ℕ))
    (blinds : Fin (22 * inputs.length + 10) → Fp × ℕ)
    (observations : Fin (22 * inputs.length) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ)
    (roundCoins : Fin 11 → (Fp × Fp) × ℕ) (scalarCoin finalBlind : Fp × ℕ)
    (coinRead : ℕ) (hch : Challenges.ReadBound ch coinRead)
    (hblinds : ∀ index, (blinds index).2 ≤ coinRead)
    (hobservations : ∀ column index, (observations column index).2 ≤ coinRead)
    (hlinear : linear.2 ≤ coinRead) (hfirst : firstGroup.2 ≤ coinRead)
    (hroundCoins : ∀ index, (roundCoins index).2 ≤ coinRead)
    (hscalar : scalarCoin.2 ≤ coinRead) (hblind : finalBlind.2 ≤ coinRead) :
    (storedActionJointSimulatorCosted fieldCosts ipaCosts node equal read omegaAccess inputs
      (StoredPlonkSetup.encode generators W U fixed sigma) key ch blinds observations linear firstGroup
      roundCoins scalarCoin finalBlind).2 ≤
      plonkJointSimulatorCostBudget fieldCosts ipaCosts node equal read omegaAccess inputs.length
        (storedActionJointInputBudget inputs.length coinRead read) (read + 1) key ch := by
  let setup := StoredPlonkSetup.encode generators W U fixed sigma
  let access := storedActionJointInputBudget inputs.length coinRead read
  have hcoin : coinRead ≤ access := by dsimp only [access, storedActionJointInputBudget]; omega
  have hread : read + 1 ≤ access := by dsimp only [access, storedActionJointInputBudget]; omega
  have hrows : ∀ action row, (actionStoredInstanceRowCosted read inputs action row).2 ≤ access := by
    intro action row
    have h := actionStoredInstanceRowCosted_cost_le read inputs action row
    dsimp only [access, storedActionJointInputBudget]
    omega
  have hfixed : ∀ column row, (setup.fixedCosted read column row).2 ≤ access := by
    intro column row
    have h := StoredPlonkSetup.fixedCosted_encode_cost_le generators W U fixed sigma read column row
    change (setup.fixedCosted read column row).2 ≤ _ at h
    dsimp only [access, storedActionJointInputBudget]
    omega
  have hsigma : ∀ column row, (setup.sigmaCosted read column row).2 ≤ access := by
    intro column row
    have h := StoredPlonkSetup.sigmaCosted_encode_cost_le generators W U fixed sigma read column row
    change (setup.sigmaCosted read column row).2 ≤ _ at h
    dsimp only [access, storedActionJointInputBudget]
    omega
  have hgenerators : ∀ index, (setup.generatorCosted read index).2 ≤ access := by
    intro index
    have h := StoredPlonkSetup.generatorCosted_encode_cost_le generators W U fixed sigma read index
    change (setup.generatorCosted read index).2 ≤ _ at h
    dsimp only [access, storedActionJointInputBudget]
    omega
  have hchAccess : Challenges.ReadBound ch access := by
    rcases hch with ⟨htheta, hbeta, hgamma, hy, hx, hx1, hx2, hx3, hx4, hxi, hz, hrounds⟩
    exact ⟨htheta.trans hcoin, hbeta.trans hcoin, hgamma.trans hcoin, hy.trans hcoin,
      hx.trans hcoin, hx1.trans hcoin, hx2.trans hcoin, hx3.trans hcoin, hx4.trans hcoin,
      hxi.trans hcoin, hz.trans hcoin, fun index => (hrounds index).trans hcoin⟩
  exact plonkJointSimulatorCosted_cost_le fieldCosts ipaCosts node equal read omegaAccess
    (actionStoredInstanceRowCosted read inputs) (setup.fixedCosted read) (setup.sigmaCosted read)
    (setup.generatorCosted read) (W, read + 1) (U, read + 1) key ch blinds observations
    linear firstGroup roundCoins scalarCoin finalBlind access hrows hfixed hsigma hgenerators
    hread hread hchAccess (fun index => (hblinds index).trans hcoin)
    (fun column index => (hobservations column index).trans hcoin) (hlinear.trans hcoin) (hfirst.trans hcoin)
    (fun index => (hroundCoins index).trans hcoin) (hscalar.trans hcoin) (hblind.trans hcoin)

end Zcash.Snark.ZeroKnowledge
