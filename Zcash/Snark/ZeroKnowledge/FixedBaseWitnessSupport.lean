import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.Ecc.MulFixed.FullWidth

/-!
# Read certificates for original fixed-base window witnesses

The cell-based window callbacks read one scalar cell. Full-width callbacks use
the original window-hint builder and inherit its complete structured support.
The table, window number, and base data are fixed arguments, not environment reads.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen Zcash.Circuits
open Zcash.Circuits.Ecc

/-- The original scalar-window index depends only on the scalar cell. -/
theorem mulFixed_windowVal_support (alpha : AssignedCell Fp) (window : ℕ) :
    WitnessFunctionSupport [alpha] (fun env => MulFixed.windowVal env alpha window) :=
  (witnessFunctionSupport_readCell alpha).map (fun value => value.val / 8 ^ window % 8)

/-- The original window x-coordinate callback has the scalar cell as support. -/
theorem mulFixed_xPWit_support (table : ℕ → ℕ → Point Fp) (alpha : AssignedCell Fp) (window : ℕ) :
    WitnessFunctionSupport [alpha] (fun env => ((MulFixed.xPWit table alpha window).eval env)[0]) :=
  (mulFixed_windowVal_support alpha window).map
    (fun index => (Vector.ofFn fun k : Fin 8 => (table window k.val).x)[index]!)

/-- The original window y-coordinate callback has the same single-cell support. -/
theorem mulFixed_yPWit_support (table : ℕ → ℕ → Point Fp) (alpha : AssignedCell Fp) (window : ℕ) :
    WitnessFunctionSupport [alpha] (fun env => ((MulFixed.yPWit table alpha window).eval env)[0]) :=
  (mulFixed_windowVal_support alpha window).map
    (fun index => (Vector.ofFn fun k : Fin 8 => (table window k.val).y)[index]!)

/-- The original square-root-table callback reads the same scalar window. -/
theorem mulFixed_uWit_support (base : MulFixed.FixedBaseData) (alpha : AssignedCell Fp) (window : ℕ) :
    WitnessFunctionSupport [alpha] (fun env => ((MulFixed.uWit base alpha window).eval env)[0]) :=
  (mulFixed_windowVal_support alpha window).map
    (fun index => (Vector.ofFn fun k : Fin 8 => base.u window k.val)[index]!)

/-- The full-width index reads exactly the selected original window builder. -/
theorem mulFixed_hintWindowVal_support
    (windows : Vector (MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (window : ℕ) :
    WitnessFunctionSupport (valueBuilderReads (value := field) windows[window]!)
      (fun env => MulFixed.FullWidth.hintWindowVal env windows window) :=
  (witnessFunctionSupport_valueBuilder (value := field) windows[window]!).map (fun value => value.val % 8)

/-- The full-width x-coordinate callback inherits the selected builder's support. -/
theorem mulFixed_xPWitH_support (base : MulFixed.FixedBaseData)
    (windows : Vector (MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (window : ℕ) :
    WitnessFunctionSupport (valueBuilderReads (value := field) windows[window]!)
      (fun env => ((MulFixed.FullWidth.xPWitH base windows window).eval env)[0]) :=
  (mulFixed_hintWindowVal_support windows window).map
    (fun index => (Vector.ofFn fun k : Fin 8 => (MulFixed.windowPoint base.point window k.val).x)[index]!)

/-- The full-width y-coordinate callback inherits the selected builder's support. -/
theorem mulFixed_yPWitH_support (base : MulFixed.FixedBaseData)
    (windows : Vector (MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (window : ℕ) :
    WitnessFunctionSupport (valueBuilderReads (value := field) windows[window]!)
      (fun env => ((MulFixed.FullWidth.yPWitH base windows window).eval env)[0]) :=
  (mulFixed_hintWindowVal_support windows window).map
    (fun index => (Vector.ofFn fun k : Fin 8 => (MulFixed.windowPoint base.point window k.val).y)[index]!)

/-- The full-width square-root-table callback inherits the selected builder's support. -/
theorem mulFixed_uWitH_support (base : MulFixed.FixedBaseData)
    (windows : Vector (MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (window : ℕ) :
    WitnessFunctionSupport (valueBuilderReads (value := field) windows[window]!)
      (fun env => ((MulFixed.FullWidth.uWitH base windows window).eval env)[0]) :=
  (mulFixed_hintWindowVal_support windows window).map
    (fun index => (Vector.ofFn fun k : Fin 8 => base.u window k.val)[index]!)

end Zcash.Snark.ZeroKnowledge
