import Zcash.Snark.ZeroKnowledge.ActionBaseCopySources
import Zcash.Snark.ZeroKnowledge.NativeCopyRegions

/-!
# Annotation-free intervals of the actual Action circuit

Native copy annotations are confined to region 297. All earlier and later
source intervals retain their exact operations while discharging the predicate
from their checked region-index bounds.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- Every source interval ending before the annotated region has no native obligations. -/
theorem actionNativeCopiesSound_before (place : RegionIndex → ℕ)
    (programs : Operations Fp) (region : RegionIndex)
    (hbound : region + programs.regionCount ≤ 297) :
    CircuitNativeCopiesSound place (actionNativeAdviceCopySource place) programs region := by
  refine circuitNativeCopiesSound_outside place (actionNativeAdviceCopySource place) programs region ?_
  intro current _ hmax column row
  exact actionNativeAdviceCopySource_otherRegion place current
    (ne_of_lt (lt_of_lt_of_le hmax hbound)) column row

/-- Every source interval beginning after the annotated region has no native obligations. -/
theorem actionNativeCopiesSound_after (place : RegionIndex → ℕ)
    (programs : Operations Fp) (region : RegionIndex) (hbound : 297 < region) :
    CircuitNativeCopiesSound place (actionNativeAdviceCopySource place) programs region := by
  refine circuitNativeCopiesSound_outside place (actionNativeAdviceCopySource place) programs region ?_
  intro current hmin _ column row
  exact actionNativeAdviceCopySource_otherRegion place current
    (ne_of_gt (lt_of_lt_of_le hbound hmin)) column row

end Zcash.Snark.ZeroKnowledge
