import Zcash.Snark.ZeroKnowledge.AdviceMapScan

/-!
# Continuations of the original advice-map scan

Each continuation retains the exact map and source entries left by its checked
transitions. Completing the scan requires a proof for that remaining state; the
map cannot be reset between pieces.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- A checked scan prefix with its remaining map and entries kept as an obligation. -/
structure AdviceMapScanPiece {Entry : Type}
    (step : AdviceAliasMap → Entry → Option AdviceAliasMap)
    (roots : AdviceAliasMap) (source : List Entry) where
  remainingRoots : AdviceAliasMap
  remainingEntries : List Entry
  finish : adviceMapScan step remainingRoots remainingEntries = true →
    adviceMapScan step roots source = true

end Zcash.Snark.ZeroKnowledge
