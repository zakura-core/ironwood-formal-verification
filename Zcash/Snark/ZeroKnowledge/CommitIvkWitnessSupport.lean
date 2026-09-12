import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.CommitIvk.Main

/-!
# Read certificates for original commitment witness callbacks

The certificates use the existing evaluator equations and list every source
cell whose value determines the output. They need no range, canonicity, or
successful-witness premise; all arithmetic and bit-slice cases are covered.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The actual CommitIvk.Main.bWit callback depends only on these source cells. -/
theorem commitIvk_bWit_support (ak nk : AssignedCell Fp) :
    WitnessFunctionSupport [ak, nk]
      (fun env => ((CommitIvk.Main.bWit ak nk).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left ak = readCell right ak := agreement.cellValues ak (by simp)
  have h1 : readCell left nk = readCell right nk := agreement.cellValues nk (by simp)
  simp only [CommitIvk.Main.bWit_eval, h0, h1]

/-- The actual CommitIvk.Main.dWit callback depends only on these source cells. -/
theorem commitIvk_dWit_support (nk : AssignedCell Fp) :
    WitnessFunctionSupport [nk]
      (fun env => ((CommitIvk.Main.dWit nk).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left nk = readCell right nk := agreement.cellValues nk (by simp)
  simp only [CommitIvk.Main.dWit_eval, h0]

/-- The actual CommitIvk.Canonicity.aPrimeWit callback depends only on these source cells. -/
theorem commitIvk_aPrimeWit_support (a : AssignedCell Fp) :
    WitnessFunctionSupport [a]
      (fun env => ((CommitIvk.Canonicity.aPrimeWit a).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left a = readCell right a := agreement.cellValues a (by simp)
  simp only [CommitIvk.Canonicity.aPrimeWit_eval, h0]

/-- The actual CommitIvk.Canonicity.b2CPrimeWit callback depends only on these source cells. -/
theorem commitIvk_b2CPrimeWit_support (b2 c : AssignedCell Fp) :
    WitnessFunctionSupport [b2, c]
      (fun env => ((CommitIvk.Canonicity.b2CPrimeWit b2 c).eval env)[0]) := by
  intro left right agreement
  have h0 : readCell left b2 = readCell right b2 := agreement.cellValues b2 (by simp)
  have h1 : readCell left c = readCell right c := agreement.cellValues c (by simp)
  simp only [CommitIvk.Canonicity.b2CPrimeWit_eval, h0, h1]

end Zcash.Snark.ZeroKnowledge
