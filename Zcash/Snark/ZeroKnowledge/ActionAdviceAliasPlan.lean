import Zcash.Snark.ZeroKnowledge.AdviceAliasCollection
import Zcash.Circuits.Action.TopLevel

/-!
# Copy annotations for the fixed Action witness program

The variable-base multiplication begins at region 297. Its two incomplete halves
share base columns 0 and 1, carrying them from the preceding row. The annotations
below are data for the checker. `ActionNativeRouting` proves their exact evaluator
semantics through the complete original Action. The global alias and read-plan
checks and the native read certificates remain necessary before applying the
witness-execution theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action

/-- The shared base-coordinate source addresses of the two original incomplete multiplication halves. -/
def actionNativeAdviceCopySource (place : RegionIndex → ℕ) : NativeAdviceCopySource :=
  fun region column row =>
    if region = 297 ∧ (column.index = 0 ∨ column.index = 1) ∧ 3 ≤ row ∧ row ≤ 127 then
      some (column.toAny, (place region + row - 1 : ℕ))
    else none

/-- The actual fixed Action programs paired with copy annotations at the actual V1 placement. -/
def actionAdviceAliasPrograms : List (PlacedAdviceProgram Fp × Option AdviceAddress) :=
  let starts := actionCircuit.regionStarts
  let place := fun region => starts.getD region 0
  circuitAdviceAliases place (actionNativeAdviceCopySource place) actionCircuit.operations 0

/-- The annotations preserve every original Action witness program, target, and source-order position. -/
theorem actionAdviceAliasPrograms_erase : actionAdviceAliasPrograms.map Prod.fst =
    circuitAdvicePrograms actionCircuit.placement actionCircuit.operations 0 := by
  exact circuitAdviceAliases_erase actionCircuit.placement
    (actionNativeAdviceCopySource actionCircuit.placement) actionCircuit.operations 0

end Zcash.Snark.ZeroKnowledge
