import Zcash.Snark.ZeroKnowledge.PermutationRowConstraints
import Zcash.Snark.Soundness.Canonical.PermutationSemantics

/-!
# Copy equations imply the packed product identity

Agreement on each declared copy propagates through the keygen replay's cycle closure.
The product then changes only by a finite permutation of its factors. This direction
needs no injectivity of cell names or nonzero challenge/denominator assumption.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Finset

/-- Equal values on declared copies remain equal after one step of the replayed permutation. -/
theorem copyValues_replay {Cell Value : Type*} [DecidableEq Cell] [Fintype Cell]
    (copies : List (Cell × Cell)) (value : Cell → Value)
    (hcopies : ∀ pair ∈ copies, value pair.1 = value pair.2) (cell : Cell) :
    value cell = value (replayKeygenPermutation copies cell) := by
  have hvalues : ∀ {left right}, Relation.EqvGen (fun a b => (a, b) ∈ copies) left right →
      value left = value right := by
    intro left right hrelation
    induction hrelation with
    | rel left right hpair => exact hcopies (left, right) hpair
    | refl cell => rfl
    | symm left right _ ih => exact ih.symm
    | trans left middle right _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hsame : (replayKeygenPermutation copies).SameCycle cell (replayKeygenPermutation copies cell) :=
    ⟨(1 : ℤ), by simp⟩
  exact hvalues ((replayKeygenPermutation_sameCycle_iff copies _ _).mp hsame)

/-- A finite product over typed cells is exactly the concrete chunk, row, and column loop. -/
theorem prod_chunk_cells (chunks rows : ℕ) (width : ℕ → ℕ) (factor : ℕ → ℕ → ℕ → Fp) :
    (∏ cell : ChunkCell chunks rows width, factor cell.1 cell.2.1 cell.2.2) =
      ∏ c ∈ range chunks, ∏ i ∈ range rows, ∏ j ∈ range (width c), factor c i j := by
  have h := prod_map_chunkedCellPairs chunks rows width factor (fun _ _ _ => 0) Prod.fst
  simpa only [chunkedCellPairs, Multiset.map_map, ← Finset.prod_eq_multiset_prod, Function.comp_def] using h

end Zcash.Snark.ZeroKnowledge
