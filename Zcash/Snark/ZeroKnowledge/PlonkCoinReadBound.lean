import Zcash.Snark.ZeroKnowledge.PlonkCoinReadCost

/-!
# Concrete bounds for every private-coin reader

The common bound follows from the stored field-list length. Preparing the four
scalar coins is charged separately; they subsequently have unit stored access.
Both reads in every IPA-round pair remain in that pair's cost.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- A common bound for all original simulator coin producers. -/
def PlonkSimulatorCoinsCosted.ReadBound {actions k : ℕ}
    (coins : PlonkSimulatorCoinsCosted actions k) (access : ℕ) : Prop :=
  (∀ index, (coins.blinds index).2 ≤ access) ∧
    (∀ column index, (coins.observations column index).2 ≤ access) ∧
    coins.linear.2 ≤ access ∧ coins.firstGroup.2 ≤ access ∧
    (∀ index, (coins.roundCoins index).2 ≤ access) ∧
    coins.scalarCoin.2 ≤ access ∧ coins.finalBlind.2 ≤ access

/-- Every private-coin access has a concrete bound, including both fields in each IPA round. -/
theorem storedPlonkCoinsCosted_readBound (actions k read : ℕ)
    (fields : List Zcash.Arithmetic.Fp) (base : ℕ) :
    (storedPlonkCoinsCosted actions k read fields base).1.ReadBound (4 * fields.length + 2 * read + 25) := by
  have hsingle (slot : ℕ) :
      (storedPlonkFieldReadCosted read fields base slot).2 ≤ 4 * fields.length + 2 * read + 25 := by
    have h := storedPlonkFieldReadCosted_cost_le read fields base slot
    omega
  have hone : 1 ≤ 4 * fields.length + 2 * read + 25 := by omega
  refine ⟨fun index => hsingle index.val,
    fun column index => hsingle ((22 * actions + 10) + (column.val * 5 + index.val)),
    hone, hone, ?_, hone, hone⟩
  intro index
  have hl := storedPlonkFieldReadCosted_cost_le read fields base
    (plonkMaskSimulatorSampleCount actions + index.val * 2)
  have hr := storedPlonkFieldReadCosted_cost_le read fields base
    (plonkMaskSimulatorSampleCount actions + (index.val * 2 + 1))
  change (storedPlonkFieldReadCosted read fields base
    (plonkMaskSimulatorSampleCount actions + index.val * 2)).2 +
    (storedPlonkFieldReadCosted read fields base
      (plonkMaskSimulatorSampleCount actions + (index.val * 2 + 1))).2 + 3 ≤ _
  omega

/-- Preparation pays for all four eager scalar loads and the stored coin record. -/
theorem storedPlonkCoinsCosted_cost_le (actions k read : ℕ)
    (fields : List Zcash.Arithmetic.Fp) (base : ℕ) :
    (storedPlonkCoinsCosted actions k read fields base).2 ≤ 8 * fields.length + 4 * read + 59 := by
  have hl := storedPlonkFieldReadCosted_cost_le read fields base ((22 * actions + 10) + (22 * actions * 5))
  have hf := storedPlonkFieldReadCosted_cost_le read fields base ((22 * actions + 10) + (22 * actions * 5 + 1))
  have hb := storedPlonkFieldReadCosted_cost_le read fields base (plonkMaskSimulatorSampleCount actions + k * 2)
  have hs := storedPlonkFieldReadCosted_cost_le read fields base (plonkMaskSimulatorSampleCount actions + (k * 2 + 1))
  dsimp only [storedPlonkCoinsCosted]
  omega

end Zcash.Snark.ZeroKnowledge
