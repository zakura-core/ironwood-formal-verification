import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.SelectorCoherence

/-!
# Bounds on Action's packed selector columns

The compressor places every emitted selector in the new fixed-column suffix.
These bounds let the masking and inactive-gate proofs identify selector queries
with the compiler's actual fixed-column values.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp)

/-- Every emitted Action selector replacement uses a column in the packed suffix. -/
theorem actionCircuit_packedSelectorBounds
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) (selector : ℕ) (compressed : SelCompress)
    (hlookup : actionCircuit.selectorMap.lookup selector = some compressed) :
    14 ≤ compressed.packedCol ∧ compressed.packedCol < 29 := by
  rw [actionCircuit.selectorMap_eq_derive] at hlookup
  obtain ⟨index, hindex, hcolumn⟩ := deriveSelCompressMap_lookup_packedColumn
    actionCircuit.constraintSystem actionCircuit.n actionCircuit.selectorActivations hlookup
  rw [← actionCircuit.selectorMap_eq_derive, hpacked] at hindex
  rw [actionCircuit_numFixedColumns_eq] at hcolumn
  omega

end Zcash.Snark.ZeroKnowledge
