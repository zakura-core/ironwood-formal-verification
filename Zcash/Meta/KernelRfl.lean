import Lean.Elab.Tactic.Basic
import Lean.Meta.Closure

/-!
# Reflexivity checked by the kernel

`kernel_rfl` submits an equality's reflexivity proof directly to Lean's kernel,
which performs the definitional reduction. It is useful for finite computation
certificates that exceed the elaborator's reduction heuristics, including open
equalities whose recursive callbacks must remain arbitrary.

The auxiliary theorem is checked synchronously before the goal is closed. No
native evaluator, axiom, or unchecked theorem is used to justify the equality.
-/

namespace Zcash.Meta

open Lean Meta Elab Tactic

private def evalKernelRfl : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, _, rhs) := target.eq? | throwError "kernel_rfl expects an equality"
  if target.hasMVar then
    throwError "kernel_rfl requires an equality without unresolved metavariables"
  let candidate ← mkEqRefl rhs
  let checked ← withOptions (Elab.async.set · false) do
    mkAuxTheorem target candidate
  goal.assign checked
  replaceMainGoal []

/-- Prove an equality by definitional reduction in Lean's kernel. -/
elab "kernel_rfl" : tactic => evalKernelRfl

end Zcash.Meta
