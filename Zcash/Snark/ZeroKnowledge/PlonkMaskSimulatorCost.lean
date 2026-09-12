import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost
import Zcash.Snark.ZeroKnowledge.PlonkSimulator

/-!
# Counted, fully materialized PLONK mask simulation

The original simulator stores commitment and column entries as finite functions.
The counted version computes every one of those entries. Its finite observation
is exactly the original view, with no work left in an unevaluated output callback.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Observe every finite entry of a pre-IPA mask view as materialized lists. -/
def materializePlonkMaskView {d commitments : ℕ} {G : Type*}
    (view : PreIpaMaskView d commitments G) : List G × (List (List Fp) × (Fp × Fp)) :=
  (List.ofFn view.1, view.2.1.map List.ofFn, view.2.2)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Execute every point multiplication and disclosed-field read in the PLONK mask simulator. -/
def materializedPlonkMaskSimulatorCosted (groupScale : ℕ) {actions : ℕ}
    (W : G × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ) :
    (List G × (List (List Fp) × (Fp × Fp))) × ℕ :=
  let points := ofFnCosted fun index : Fin (22 * actions + 10) =>
    let blind := blinds index
    (blind.1 • W.1, blind.2 + W.2 + groupScale + 1)
  let columns := ofFnCosted fun column : Fin (22 * actions) => ofFnCosted (observations column)
  ((points.1, columns.1, linear.1, firstGroup.1),
    points.2 + columns.2 + linear.2 + firstGroup.2 + 1)

/-- The complete finite result is precisely the existing simulator's mask view. -/
theorem materializedPlonkMaskSimulatorCosted_result (groupScale : ℕ) {actions : ℕ}
    (W : G × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ) :
    (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1 =
      materializePlonkMaskView (plonkMaskSimulatorFromCoins W.1
        (fun index => (blinds index).1, fun column index => (observations column index).1,
          linear.1, firstGroup.1)) := by
  simp only [materializedPlonkMaskSimulatorCosted, ofFnCosted_result, materializePlonkMaskView,
    plonkMaskSimulatorFromCoins, List.map_ofFn, Function.comp_def]

/-- Every originally function-valued point is materialized. -/
theorem materializedPlonkMaskSimulatorCosted_points_length (groupScale : ℕ) {actions : ℕ}
    (W : G × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ) :
    (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.1.length =
      22 * actions + 10 := by
  simp only [materializedPlonkMaskSimulatorCosted, ofFnCosted_length]

/-- Every private column is materialized. -/
theorem materializedPlonkMaskSimulatorCosted_columns_length (groupScale : ℕ) {actions : ℕ}
    (W : G × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ) :
    (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.2.1.length =
      22 * actions := by
  simp only [materializedPlonkMaskSimulatorCosted, ofFnCosted_length]

/-- All five disclosed fields are materialized for every private column. -/
theorem materializedPlonkMaskSimulatorCosted_observations_length (groupScale : ℕ) {actions : ℕ}
    (W : G × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ)
    (column : List Fp)
    (hcolumn : column ∈
      (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).1.2.1) :
    column.length = 5 := by
  simp only [materializedPlonkMaskSimulatorCosted, ofFnCosted_result, List.mem_ofFn] at hcolumn
  obtain ⟨index, rfl⟩ := hcolumn
  simp only [List.length_ofFn]

/-- The whole mask simulation has an explicit bound in the Action count and complete coin reads. -/
theorem materializedPlonkMaskSimulatorCosted_cost_le (groupScale : ℕ) {actions : ℕ}
    (W : G × ℕ) (blinds : Fin (22 * actions + 10) → Fp × ℕ)
    (observations : Fin (22 * actions) → Fin 5 → Fp × ℕ) (linear firstGroup : Fp × ℕ)
    (access : ℕ) (hblinds : ∀ index, (blinds index).2 ≤ access)
    (hobservations : ∀ column index, (observations column index).2 ≤ access)
    (hlinear : linear.2 ≤ access) (hfirstGroup : firstGroup.2 ≤ access) :
    (materializedPlonkMaskSimulatorCosted groupScale W blinds observations linear firstGroup).2 ≤
      (22 * actions + 10) * (access + W.2 + groupScale + 2) +
        (22 * actions + 10) * (22 * actions + 10) +
        (22 * actions) * (5 * access + 32) + (22 * actions) * (22 * actions) + 2 * access + 3 := by
  have hpoint (index : Fin (22 * actions + 10)) :
      (blinds index).2 + W.2 + groupScale + 1 ≤ access + W.2 + groupScale + 1 := by
    have h := hblinds index
    omega
  have hpoints := ofFnCosted_cost_le (fun index : Fin (22 * actions + 10) =>
    ((blinds index).1 • W.1, (blinds index).2 + W.2 + groupScale + 1))
    (access + W.2 + groupScale + 1) hpoint
  have hcolumn (column : Fin (22 * actions)) :
      (ofFnCosted (observations column)).2 ≤ 5 * access + 31 := by
    have h := ofFnCosted_cost_le (observations column) access (hobservations column)
    omega
  have hcolumns := ofFnCosted_cost_le (fun column : Fin (22 * actions) =>
    ofFnCosted (observations column)) (5 * access + 31) hcolumn
  simp only [materializedPlonkMaskSimulatorCosted]
  nlinarith

end Zcash.Snark.ZeroKnowledge
