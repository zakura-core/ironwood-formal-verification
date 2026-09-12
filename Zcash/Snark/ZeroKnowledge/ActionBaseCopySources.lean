import Zcash.Snark.ZeroKnowledge.ActionAdviceAliasPlan
import Zcash.Snark.ZeroKnowledge.NativeBaseCopySupport

/-!
# Copy-source boundaries for the fixed Action

The native annotations select only the variable-base region and its shared base
rows. Their addresses are exactly those required by the generic preceding-row
certificate.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- All other Action regions have no native copy annotations. -/
theorem actionNativeAdviceCopySource_otherRegion (place : RegionIndex → ℕ)
    (region : RegionIndex) (hregion : region ≠ 297) (column : Column .advice) (row : ℕ) :
    actionNativeAdviceCopySource place region column row = none := by
  simp [actionNativeAdviceCopySource, hregion]

/-- The exact Action annotation is a preceding-row copy in a base column. -/
theorem actionNativeAdviceCopySource_previous (place : RegionIndex → ℕ)
    (region : RegionIndex) (baseX baseY : Column .advice)
    (hx : baseX.index = 0) (hy : baseY.index = 1) :
    PreviousBaseCopySources place (actionNativeAdviceCopySource place) region baseX baseY := by
  intro column row address htag
  unfold actionNativeAdviceCopySource at htag
  split at htag
  · rename_i h
    constructor
    · rcases h.2.1 with h0 | h1
      · left
        cases column
        cases baseX
        simp_all
      · right
        cases column
        cases baseY
        simp_all
    · rw [← Option.some.inj htag]
      apply Prod.ext
      · rfl
      · dsimp only
        exact_mod_cast (show place region + row - 1 = place region + (row - 1) by omega)
  · cases htag

/-- Rows outside the shared incomplete rounds have no native annotations. -/
theorem actionNativeAdviceCopySource_outsideRows (place : RegionIndex → ℕ)
    (region : RegionIndex) (column : Column .advice) (row : ℕ)
    (hrow : row < 3 ∨ 127 < row) :
    actionNativeAdviceCopySource place region column row = none := by
  unfold actionNativeAdviceCopySource
  split
  · rename_i h
    omega
  · rfl

end Zcash.Snark.ZeroKnowledge
