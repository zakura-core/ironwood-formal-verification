import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.Poseidon.Hash

/-!
# Read certificates for the original Poseidon native callbacks

These certificates concern the existing witness programs, including arbitrary
round functions. The three entering state cells determine each round output;
constants, initial-state additions, and copies have their exact smaller supports.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2
open Zcash.Circuits

/-- A constant native witness reads no advice cell. -/
theorem poseidon_constWit_support (value : Fp) :
    WitnessFunctionSupport [] (fun env => ((Poseidon.constWit value).eval env)[0]) := by
  intro left right _
  simp only [Poseidon.constWit_eval]

/-- The actual initial-state addition depends on its two source cells. -/
theorem poseidon_addWit_support (a b : AssignedCell Fp) :
    WitnessFunctionSupport [a, b] (fun env => ((Poseidon.addWit a b).eval env)[0]) := by
  intro left right agreement
  have ha : readCell left a = readCell right a := agreement.cellValues a (by simp)
  have hb : readCell left b = readCell right b := agreement.cellValues b (by simp)
  simp only [Poseidon.addWit_eval, ha, hb]

/-- The native copy callback depends only on the copied cell. -/
theorem poseidon_readCellWit_support (cell : AssignedCell Fp) :
    WitnessFunctionSupport [cell] (fun env => ((Poseidon.readCellWit cell).eval env)[0]) := by
  intro left right agreement
  simpa only [Poseidon.readCellWit_eval] using agreement.cellValues cell (List.mem_singleton_self _)

/-- All original full/partial round callbacks are functions of the same three entering cells. -/
theorem poseidon_rowWit_support (row : Poseidon.Permute.State (AssignedCell Fp))
    (f : Poseidon.Permute.State Fp → Fp) :
    WitnessFunctionSupport [row.x0, row.x1, row.x2]
      (fun env => ((Poseidon.rowWit row f).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left row.x0 = readCell right row.x0 := agreement.cellValues row.x0 (by simp)
  have h1 : readCell left row.x1 = readCell right row.x1 := agreement.cellValues row.x1 (by simp)
  have h2 : readCell left row.x2 = readCell right row.x2 := agreement.cellValues row.x2 (by simp)
  simp only [Poseidon.rowWit_eval, Poseidon.rowValue, h0, h1, h2]

end Zcash.Snark.ZeroKnowledge
