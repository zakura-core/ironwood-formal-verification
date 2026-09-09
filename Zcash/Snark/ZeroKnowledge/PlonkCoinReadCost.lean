import Zcash.Snark.ZeroKnowledge.PlonkSimulatorTape
import Zcash.Snark.ZeroKnowledge.ListRoutingCost

/-!
# Exact private-coin routing from a stored field tape

The slot formulas follow the original nested tape split. Each read pays for
traversing the stored list and ten structural units covering the fixed-depth
index formulas and reader adapters below. Four scalar coins are loaded during
preparation; every later functional coin access retains its complete read cost.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- The original private-coin families with complete producer/read costs attached. -/
structure PlonkSimulatorCoinsCosted (actions k : ℕ) where
  blinds : Fin (22 * actions + 10) → Fp × ℕ
  observations : Fin (22 * actions) → Fin 5 → Fp × ℕ
  linear : Fp × ℕ
  firstGroup : Fp × ℕ
  roundCoins : Fin k → (Fp × Fp) × ℕ
  scalarCoin : Fp × ℕ
  finalBlind : Fp × ℕ

/-- Erase the attached costs in the original simulator's coin tuple order. -/
def PlonkSimulatorCoinsCosted.erase {actions k : ℕ} (coins : PlonkSimulatorCoinsCosted actions k) :
    PlonkMaskSimulatorCoins actions × (((Fin k → Fp × Fp) × Fp) × Fp) :=
  ((fun index => (coins.blinds index).1,
    fun column index => (coins.observations column index).1, coins.linear.1, coins.firstGroup.1),
    (fun index => (coins.roundCoins index).1, coins.finalBlind.1), coins.scalarCoin.1)

/-- Read a stored field at its private-tape offset with the fixed slot-arithmetic charge. -/
def storedPlonkFieldReadCosted (read : ℕ) (fields : List Fp) (base slot : ℕ) : Fp × ℕ :=
  let value := getDListCosted read (0 : Fp) fields (base + slot)
  (value.1, value.2 + 10)

/-- Slot reading preserves the original stored-list default. -/
theorem storedPlonkFieldReadCosted_result (read : ℕ) (fields : List Fp) (base slot : ℕ) :
    (storedPlonkFieldReadCosted read fields base slot).1 = fields.getD (base + slot) 0 :=
  getDListCosted_result _ _ _ _

/-- Every slot access is bounded by the actual stored field-list length. -/
theorem storedPlonkFieldReadCosted_cost_le (read : ℕ) (fields : List Fp) (base slot : ℕ) :
    (storedPlonkFieldReadCosted read fields base slot).2 ≤ 2 * fields.length + read + 11 := by
  have h := getDListCosted_cost_le read (0 : Fp) fields (base + slot)
  dsimp only [storedPlonkFieldReadCosted]
  omega

/-- Prepare scalar coins and retain full indexed readers for every other original coin slot. -/
def storedPlonkCoinsCosted (actions k read : ℕ) (fields : List Fp) (base : ℕ) :
    PlonkSimulatorCoinsCosted actions k × ℕ :=
  let pointCount := 22 * actions + 10
  let observationCount := 22 * actions * 5
  let maskCount := plonkMaskSimulatorSampleCount actions
  let linear := storedPlonkFieldReadCosted read fields base (pointCount + observationCount)
  let firstGroup := storedPlonkFieldReadCosted read fields base (pointCount + (observationCount + 1))
  let finalBlind := storedPlonkFieldReadCosted read fields base (maskCount + k * 2)
  let scalarCoin := storedPlonkFieldReadCosted read fields base (maskCount + (k * 2 + 1))
  ({ blinds := fun index => storedPlonkFieldReadCosted read fields base index.val,
      observations := fun column index =>
        storedPlonkFieldReadCosted read fields base (pointCount + (column.val * 5 + index.val)),
      linear := (linear.1, 1), firstGroup := (firstGroup.1, 1),
      roundCoins := fun index =>
        let left := storedPlonkFieldReadCosted read fields base (maskCount + index.val * 2)
        let right := storedPlonkFieldReadCosted read fields base (maskCount + (index.val * 2 + 1))
        ((left.1, right.1), left.2 + right.2 + 3),
      scalarCoin := (scalarCoin.1, 1), finalBlind := (finalBlind.1, 1) },
    linear.2 + firstGroup.2 + finalBlind.2 + scalarCoin.2 + 15)

/-- The stored readers implement the exact existing split, including the two final scalar positions. -/
theorem storedPlonkCoinsCosted_result (actions k read : ℕ) (fields : List Fp) (base : ℕ) :
    (storedPlonkCoinsCosted actions k read fields base).1.erase =
      plonkSimulatorTapeEquiv actions k (fun index => fields.getD (base + index.val) 0) := by
  simp only [storedPlonkCoinsCosted, PlonkSimulatorCoinsCosted.erase, storedPlonkFieldReadCosted_result]
  change _ =
    ((fun index : Fin (22 * actions + 10) => fields.getD (base + index.val) 0,
      fun (column : Fin (22 * actions)) (index : Fin 5) =>
        fields.getD (base + ((22 * actions + 10) + (index.val + 5 * column.val))) 0,
      fields.getD (base + ((22 * actions + 10) + (22 * actions * 5))) 0,
      fields.getD (base + ((22 * actions + 10) + (22 * actions * 5 + 1))) 0),
      (fun index : Fin k =>
        (fields.getD (base + (plonkMaskSimulatorSampleCount actions + (0 + 2 * index.val))) 0,
          fields.getD (base + (plonkMaskSimulatorSampleCount actions + (1 + 2 * index.val))) 0),
        fields.getD (base + (plonkMaskSimulatorSampleCount actions + k * 2)) 0),
      fields.getD (base + (plonkMaskSimulatorSampleCount actions + (k * 2 + 1))) 0)
  simp only [Nat.zero_add, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end Zcash.Snark.ZeroKnowledge
