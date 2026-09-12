import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.NoteCommit.YComposite
import Zcash.Circuits.NoteCommit.Composites

/-!
# Read certificates for original commitment witness callbacks

The certificates use the existing evaluator equations and list every source
cell whose value determines the output. They need no range, canonicity, or
successful-witness premise; all arithmetic and bit-slice cases are covered.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The actual NoteCommit.GdCanonicityCheck.aPrimeWit callback depends only on these source cells. -/
theorem note_aPrimeWit_support (a : AssignedCell Fp) :
    WitnessFunctionSupport [a]
      (fun env => ((NoteCommit.GdCanonicityCheck.aPrimeWit a).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left a = readCell right a := agreement.cellValues a (by simp)
  simp only [NoteCommit.GdCanonicityCheck.aPrimeWit_eval, h0]

/-- The actual NoteCommit.PkdCanonicityCheck.b3CPrimeWit callback depends only on these source cells. -/
theorem note_b3CPrimeWit_support (b3 c : AssignedCell Fp) :
    WitnessFunctionSupport [b3, c]
      (fun env => ((NoteCommit.PkdCanonicityCheck.b3CPrimeWit b3 c).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left b3 = readCell right b3 := agreement.cellValues b3 (by simp)
  have h1 : readCell left c = readCell right c := agreement.cellValues c (by simp)
  simp only [NoteCommit.PkdCanonicityCheck.b3CPrimeWit_eval, h0, h1]

/-- The actual NoteCommit.RhoCanonicityCheck.e1FPrimeWit callback depends only on these source cells. -/
theorem note_e1FPrimeWit_support (e1 f : AssignedCell Fp) :
    WitnessFunctionSupport [e1, f]
      (fun env => ((NoteCommit.RhoCanonicityCheck.e1FPrimeWit e1 f).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left e1 = readCell right e1 := agreement.cellValues e1 (by simp)
  have h1 : readCell left f = readCell right f := agreement.cellValues f (by simp)
  simp only [NoteCommit.RhoCanonicityCheck.e1FPrimeWit_eval, h0, h1]

/-- The actual NoteCommit.PsiCanonicityCheck.g1G2PrimeWit callback depends only on these source cells. -/
theorem note_g1G2PrimeWit_support (g1 g2 : AssignedCell Fp) :
    WitnessFunctionSupport [g1, g2]
      (fun env => ((NoteCommit.PsiCanonicityCheck.g1G2PrimeWit g1 g2).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left g1 = readCell right g1 := agreement.cellValues g1 (by simp)
  have h1 : readCell left g2 = readCell right g2 := agreement.cellValues g2 (by simp)
  simp only [NoteCommit.PsiCanonicityCheck.g1G2PrimeWit_eval, h0, h1]

/-- The actual NoteCommit.YCanonicityCheck.k0Wit callback depends only on these source cells. -/
theorem note_k0Wit_support (y : AssignedCell Fp) :
    WitnessFunctionSupport [y]
      (fun env => ((NoteCommit.YCanonicityCheck.k0Wit y).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left y = readCell right y := agreement.cellValues y (by simp)
  simp only [NoteCommit.YCanonicityCheck.k0Wit_eval, h0]

/-- The actual NoteCommit.YCanonicityCheck.k2Wit callback depends only on these source cells. -/
theorem note_k2Wit_support (y : AssignedCell Fp) :
    WitnessFunctionSupport [y]
      (fun env => ((NoteCommit.YCanonicityCheck.k2Wit y).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left y = readCell right y := agreement.cellValues y (by simp)
  simp only [NoteCommit.YCanonicityCheck.k2Wit_eval, h0]

/-- The actual NoteCommit.YCanonicityCheck.k3Wit callback depends only on these source cells. -/
theorem note_k3Wit_support (y : AssignedCell Fp) :
    WitnessFunctionSupport [y]
      (fun env => ((NoteCommit.YCanonicityCheck.k3Wit y).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left y = readCell right y := agreement.cellValues y (by simp)
  simp only [NoteCommit.YCanonicityCheck.k3Wit_eval, h0]

/-- The actual NoteCommit.YCanonicityCheck.jPrimeWit callback depends only on these source cells. -/
theorem note_jPrimeWit_support (j : AssignedCell Fp) :
    WitnessFunctionSupport [j]
      (fun env => ((NoteCommit.YCanonicityCheck.jPrimeWit j).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left j = readCell right j := agreement.cellValues j (by simp)
  simp only [NoteCommit.YCanonicityCheck.jPrimeWit_eval, h0]

/-- The low-bit callback retains its own certified reads inside the original y-coordinate computation. -/
theorem note_jWit_support (lowBit : WitgenIR Fp 1) (y : AssignedCell Fp)
    (reads : List (AssignedCell Fp))
    (support : WitnessFunctionSupport reads (fun env => (lowBit.eval env)[0])) :
    WitnessFunctionSupport (reads ++ [y])
      (fun env => ((NoteCommit.YCanonicityCheck.jWit lowBit y).eval env)[0]) := by
  intro left right agreement
  have hbit := support left right agreement.left
  have hy : readCell left y = readCell right y := agreement.right.cellValues y (by simp)
  simp only [NoteCommit.YCanonicityCheck.jWit_eval, hbit, hy]

end Zcash.Snark.ZeroKnowledge
