import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.NoteCommit.Main

/-!
# Read certificates for original commitment witness callbacks

The certificates use the existing evaluator equations and list every source
cell whose value determines the output. They need no range, canonicity, or
successful-witness premise; all arithmetic and bit-slice cases are covered.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The actual NoteCommit.Main.brWit callback depends only on these source cells. -/
theorem note_brWit_support (cell : AssignedCell Fp) (offset width : ℕ):
    WitnessFunctionSupport [cell]
      (fun env => ((NoteCommit.Main.brWit cell offset width).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left cell = readCell right cell := agreement.cellValues cell (by simp)
  simp only [NoteCommit.Main.brWit_eval, h0]

/-- The actual NoteCommit.Main.bWit callback depends only on these source cells. -/
theorem note_bWit_support (gx gy px : AssignedCell Fp) :
    WitnessFunctionSupport [gx, gy, px]
      (fun env => ((NoteCommit.Main.bWit gx gy px).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left gx = readCell right gx := agreement.cellValues gx (by simp)
  have h1 : readCell left gy = readCell right gy := agreement.cellValues gy (by simp)
  have h2 : readCell left px = readCell right px := agreement.cellValues px (by simp)
  simp only [NoteCommit.Main.bWit_eval, h0, h1, h2]

/-- The actual NoteCommit.Main.dWit callback depends only on these source cells. -/
theorem note_dWit_support (px py value : AssignedCell Fp) :
    WitnessFunctionSupport [px, py, value]
      (fun env => ((NoteCommit.Main.dWit px py value).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left px = readCell right px := agreement.cellValues px (by simp)
  have h1 : readCell left py = readCell right py := agreement.cellValues py (by simp)
  have h2 : readCell left value = readCell right value := agreement.cellValues value (by simp)
  simp only [NoteCommit.Main.dWit_eval, h0, h1, h2]

/-- The actual NoteCommit.Main.eWit callback depends only on these source cells. -/
theorem note_eWit_support (value rho : AssignedCell Fp) :
    WitnessFunctionSupport [value, rho]
      (fun env => ((NoteCommit.Main.eWit value rho).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left value = readCell right value := agreement.cellValues value (by simp)
  have h1 : readCell left rho = readCell right rho := agreement.cellValues rho (by simp)
  simp only [NoteCommit.Main.eWit_eval, h0, h1]

/-- The actual NoteCommit.Main.gWit callback depends only on these source cells. -/
theorem note_gWit_support (rho psi : AssignedCell Fp) :
    WitnessFunctionSupport [rho, psi]
      (fun env => ((NoteCommit.Main.gWit rho psi).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left rho = readCell right rho := agreement.cellValues rho (by simp)
  have h1 : readCell left psi = readCell right psi := agreement.cellValues psi (by simp)
  simp only [NoteCommit.Main.gWit_eval, h0, h1]

/-- The actual NoteCommit.Main.hWit callback depends only on these source cells. -/
theorem note_hWit_support (psi : AssignedCell Fp) :
    WitnessFunctionSupport [psi]
      (fun env => ((NoteCommit.Main.hWit psi).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left psi = readCell right psi := agreement.cellValues psi (by simp)
  simp only [NoteCommit.Main.hWit_eval, h0]

end Zcash.Snark.ZeroKnowledge
