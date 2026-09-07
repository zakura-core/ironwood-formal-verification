import Clean.Halo2.TopLevel

/-!
# Region starts from the compositional synthesis summary

The compiler's exact ordered placement can be obtained from its proved summary.
This equality avoids evaluating witness programs and preserves V1's sorting and
region-index restoration, including the order of regions with equal sort keys.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner

/-- V1 applied to an ordered summary. Keep the planner opaque, just as the
compiler does for its operation-based entry point. -/
irreducible_def regionStartsFromSummary (summary : SynthesisSummary) : List ℕ :=
  (V1.planCandidate (indexRegionSummaries 0 summary.regionShapes)).1

/-- The reduced, ordered summary supplies exactly the actual compiler's region starts. -/
theorem topLevel_regionStarts_eq_planSummary {F Config : Type} [FiniteField F]
    {PublicInput : TypeMap} [ProvableType PublicInput]
    (circuit : TopLevelCircuit F Config PublicInput) :
    circuit.regionStarts = regionStartsFromSummary circuit.synthesisSummary := by
  rw [regionStartsFromSummary]
  change (V1.planOperations circuit.operations).1 = _
  exact congrArg Prod.fst ((V1.planOperations_eq circuit.operations).trans
    (congrArg V1.planCandidate circuit.plannerShapes_eq_measureRegions.symm))

end Zcash.Snark.ZeroKnowledge
