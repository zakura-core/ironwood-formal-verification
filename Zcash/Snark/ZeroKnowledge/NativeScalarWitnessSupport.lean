import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.Utilities.AddChip

/-!
# Native scalar wrappers and original addition witnesses

The constant and Boolean wrappers cover the anonymous native callbacks used by
the Merkle level and conditional-swap gadgets. The Boolean wrapper retains the
support of the supplied function; it never assumes that function reads nothing.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The exact one-element native wrapper preserves its scalar function's support. -/
theorem nativeScalar_support (reads : List (AssignedCell Fp))
    (compute : Placed ProverEnvironment Fp → Fp) (support : WitnessFunctionSupport reads compute) :
    WitnessFunctionSupport reads
      (fun env => ((.native (fun input => #v[compute input]) : WitgenIR Fp 1).eval env)[0]) := support

/-- Anonymous constant callbacks need no cell input. -/
theorem nativeConstant_support (value : Fp) :
    WitnessFunctionSupport [] (fun env => ((.native (fun _ => #v[value]) : WitgenIR Fp 1).eval env)[0]) :=
  witnessFunctionSupport_const value

/-- The conditional-swap flag wrapper retains all reads of its actual Boolean callback. -/
theorem nativeBoolean_support (reads : List (AssignedCell Fp))
    (compute : Placed ProverEnvironment Fp → Bool) (support : WitnessFunctionSupport reads compute) :
    WitnessFunctionSupport reads (fun env =>
      ((.native (fun input => #v[if compute input then (1 : Fp) else 0]) : WitgenIR Fp 1).eval env)[0]) :=
  support.map (fun value => if value then (1 : Fp) else 0)

/-- The original utility addition callback depends on the two cells it adds. -/
theorem addChip_sumWit_support (a b : AssignedCell Fp) :
    WitnessFunctionSupport [a, b] (fun env => ((AddChip.sumWit a b).eval env)[0]) := by
  intro left right agreement
  have ha : readCell left a = readCell right a := agreement.cellValues a (by simp)
  have hb : readCell left b = readCell right b := agreement.cellValues b (by simp)
  simp only [AddChip.sumWit_eval, ha, hb]

end Zcash.Snark.ZeroKnowledge
