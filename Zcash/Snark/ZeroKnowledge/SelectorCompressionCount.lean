import Clean.Halo2.Keygen.CompressSelectors

/-!
# The selector-compression count as a finite calculation

The number of appended columns depends only on the selector degrees, degree
budget, domain size, and activation rows. Keeping this calculation opaque avoids
accidentally evaluating the packer during elaboration of its input refinements.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Count the columns allocated by the actual greedy packer from its finite inputs. -/
irreducible_def selectorPackingCount (rows selectors budget : ℕ)
    (degrees : Array ℕ) (activations : List (ℕ × ℕ)) : ℕ :=
  let table := activationTable rows selectors activations
  let descriptions := (List.range selectors).map fun index =>
    SelectorDescription.mk index table[index]! degrees[index]!
  (process descriptions budget).newFixedCols

/-- The compiler's appended-column count is exactly this finite packing calculation. -/
theorem deriveSelCompressMap_newFixedCols_eq_count {F : Type}
    (cs : ConstraintSystem F) (rows : ℕ) (activations : List (ℕ × ℕ)) :
    (deriveSelCompressMap cs rows activations).newFixedCols =
      selectorPackingCount rows cs.numSelectors (csDegree cs) (selectorMaxDegrees cs) activations := by
  rw [selectorPackingCount]
  rfl

end Zcash.Snark.ZeroKnowledge
