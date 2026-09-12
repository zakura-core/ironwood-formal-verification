import Zcash.Snark.ZeroKnowledge.PlonkMaskSimulatorCost
import Zcash.Snark.ZeroKnowledge.StoredRowsCost

/-!
# Bounds derived from the jointly simulated stored mask

The input to these readers is the actual materialized mask simulator output.
Consequently its dimensions and every generated reader bound follow from the
constructor; no independent correctness or size premise is required.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]
variable (groupScale : ℕ) {actions : ℕ} (W : G × ℕ)
  (blinds : Fin (22 * actions + 10) → Fp × ℕ)
  (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ) (read : ℕ)

/-- The stored observation readers cover exactly the original private-column family. -/
theorem plonkMaskStoredViews_length :
    (storedRowReadersCosted read (0 : Fp) 5
      (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.2.1).1.length =
      22 * actions := by
  rw [storedRowReadersCosted_length, materializedPlonkMaskSimulatorCosted_columns_length]

/-- Reader preparation is bounded by the original private-column count. -/
theorem plonkMaskStoredViews_cost_le :
    (storedRowReadersCosted read (0 : Fp) 5
      (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.2.1).2 ≤
      (22 * actions) * 3 + 1 := by
  have h := storedRowReadersCosted_cost_le read (0 : Fp) 5
    (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.2.1
  rw [materializedPlonkMaskSimulatorCosted_columns_length] at h
  exact h

/-- Each eventual observation access pays for its actual five-entry stored row. -/
theorem plonkMaskStoredViews_readBound (column : Fin 5 → Fp × ℕ)
    (hcolumn : column ∈ (storedRowReadersCosted read (0 : Fp) 5
      (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.2.1).1)
    (point : Fin 5) : (column point).2 ≤ read + 11 := by
  have h := storedRowReadersCosted_readBound read (0 : Fp) 5
    (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.2.1
    5 (fun values hmem =>
      (materializedPlonkMaskSimulatorCosted_observations_length groupScale W blinds observations
        linear firstGroup values hmem).le) column hcolumn point
  omega

/-- Each eventual point access pays for the complete stored commitment family. -/
theorem plonkMaskStoredPoints_cost_le (index : Fin (22 * actions + 10)) :
    (getDListCosted read (0 : G)
      (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.1 index.val).2 ≤
      44 * actions + read + 21 := by
  have h := getDListCosted_cost_le read (0 : G)
    (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.1 index.val
  rw [materializedPlonkMaskSimulatorCosted_points_length] at h
  omega

end Zcash.Snark.ZeroKnowledge
