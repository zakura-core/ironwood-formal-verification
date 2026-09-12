import Zcash.Snark.ZeroKnowledge.NativeCopyComposition

/-!
# Region-indexed native copy-source certificates

Composition preserves the source circuit's exact region counter. A source interval
with no annotations imposes no native-copy obligation on any of its operations.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- Source-list concatenation advances by exactly the number of regions on its left. -/
theorem circuitNativeCopiesSound_append {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (left right : Operations F) (region : RegionIndex) :
    CircuitNativeCopiesSound place source (left ++ right) region ↔
      CircuitNativeCopiesSound place source left region ∧
      CircuitNativeCopiesSound place source right (region + left.regionCount) := by
  induction left generalizing region with
  | nil => simp [CircuitNativeCopiesSound, Operations.regionCount]
  | cons operation rest ih =>
    cases operation <;>
      simp [CircuitNativeCopiesSound, Operations.regionCount, ih, Nat.add_assoc, and_assoc]

/-- A region interval on which the source annotator is empty has no native obligations. -/
theorem circuitNativeCopiesSound_outside {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (source : NativeAdviceCopySource)
    (programs : Operations F) (region : RegionIndex)
    (hnone : ∀ current, region ≤ current → current < region + programs.regionCount →
      ∀ column row, source current column row = none) :
    CircuitNativeCopiesSound place source programs region := by
  induction programs generalizing region with
  | nil => trivial
  | cons operation rest ih =>
    cases operation with
    | region name body =>
      constructor
      · apply regionNativeCopiesSound_of_none
        exact hnone region le_rfl (by simp [Operations.regionCount])
      · apply ih
        intro current hmin hmax column row
        exact hnone current (Nat.le_trans (Nat.le_succ _) hmin) (by simpa [Operations.regionCount, Nat.add_assoc] using hmax) column row
    | constrainInstance cell column row =>
      apply ih
      exact hnone
    | loadTable column table =>
      apply ih
      exact hnone

end Zcash.Snark.ZeroKnowledge
