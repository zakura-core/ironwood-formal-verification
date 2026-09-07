import Zcash.Snark.ZeroKnowledge.SelectorActivationBits
import Zcash.Snark.ZeroKnowledge.SelectorCompressionCount

/-!
# The selector packing count through activation bit vectors

Only the activation-table representation changes in this calculation. The
compiler's degree order, greedy combination loop, and final column count remain
the same. Conflict tests on decoded rows can use the checked bitwise-intersection
lemma from `SelectorActivationBits`.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Evaluate the original packer after decoding the compact activation table. -/
irreducible_def selectorBitPackingCount (rows selectors budget : ℕ)
    (degrees : Array ℕ) (activations : List (ℕ × ℕ)) : ℕ :=
  let table := selectorActivationBits rows selectors activations
  let descriptions := (List.range selectors).map fun index =>
    SelectorDescription.mk index (selectorBitsRows table[index]!) degrees[index]!
  (process descriptions budget).newFixedCols

/-- The compact calculation returns exactly the original compiler packing count. -/
theorem selectorPackingCount_eq_bits (rows selectors budget : ℕ)
    (degrees : Array ℕ) (activations : List (ℕ × ℕ)) :
    selectorPackingCount rows selectors budget degrees activations =
      selectorBitPackingCount rows selectors budget degrees activations := by
  rw [selectorPackingCount, selectorBitPackingCount, activationTable_eq_selectorBitsRows]
  apply congrArg (fun descriptions => (process descriptions budget).newFixedCols)
  apply List.map_congr_left
  intro index hindex
  let table := selectorActivationBits rows selectors activations
  have hbound : index < table.size := by
    rw [selectorActivationBits_size]
    exact List.mem_range.mp hindex
  have hread : (table.map selectorBitsRows)[index]! = selectorBitsRows table[index]! := by
    rw [getElem!_pos (table.map selectorBitsRows) index (by simpa using hbound),
      Array.getElem_map, getElem!_pos table index hbound]
  change SelectorDescription.mk index (table.map selectorBitsRows)[index]! degrees[index]! =
    SelectorDescription.mk index (selectorBitsRows table[index]!) degrees[index]!
  rw [hread]

end Zcash.Snark.ZeroKnowledge
