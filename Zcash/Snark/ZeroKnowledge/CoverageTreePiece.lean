import Zcash.Snark.ZeroKnowledge.ActivationCoverageData

/-!
# Comparison-tree state across declaration boundaries

A piece preserves both the accumulated comparison tree and every remaining
label. Its continuation identifies the result of the original complete fold
only after the remaining fold has been checked.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- A checked prefix of the original comparison-tree construction. -/
structure CoverageTreePiece {α : Type} (cmp : α → α → Ordering)
    (source : List α) (initial : Std.TreeSet α cmp) where
  remainingEntries : List α
  remainingTree : Std.TreeSet α cmp
  finish : ∀ final, coverageTreeFold cmp remainingEntries remainingTree = final →
    coverageTreeFold cmp source initial = final

end Zcash.Snark.ZeroKnowledge
