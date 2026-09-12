import Zcash.Snark.ZeroKnowledge.ActionSourceSelectorTrace
import Zcash.Snark.ZeroKnowledge.SelectorTracePlacement
import Zcash.Circuits.Action.Planner

/-!
# Action activation placement from the reduced source data

The exact V1 input order comes from the Action bundle's compositional summary.
Combining it with the source selector trace gives the complete activation list
without unfolding the full operation stream. No numerical packing certificate is
assumed or established by this refinement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner Zcash.Circuits.Action

/-- V1 placement of the source-derived Action region shapes, in synthesis order. -/
def actionSourceRegionStarts : List ℕ :=
  regionStartsFromSummary (Circuit.mainPostSynthesisSummary actionConfig)

/-- The controlled computation equation for the concrete source-summary placement. -/
theorem actionSourceRegionStarts_def :
    actionSourceRegionStarts = (V1.planCandidate (indexRegionSummaries 0
      (Circuit.mainPostSynthesisSummary actionConfig).regionShapes)).1 :=
  regionStartsFromSummary_def _

/-- The source-summary calculation gives the actual opaque Action circuit's starts. -/
theorem actionCircuit_regionStarts_eq_source :
    actionCircuit.regionStarts = actionSourceRegionStarts :=
  (topLevel_regionStarts_eq_planSummary actionCircuit).trans
    (congrArg regionStartsFromSummary actionCircuit_synthesisSummary_eq)

/-- The complete absolute activation list computed from reduced Action source data. -/
def actionSourceSelectorActivations : List (ℕ × ℕ) :=
  placeSelectorTrace actionSourceRegionStarts (actionSourceSelectorTrace actionConfig)

/-- The source activation list preserves exactly the source trace and ordered placement. -/
theorem actionSourceSelectorActivations_def :
    actionSourceSelectorActivations =
      placeSelectorTrace actionSourceRegionStarts (actionSourceSelectorTrace actionConfig) := rfl

/-- Both synthesis and placement agree with the source-derived activation list. -/
theorem actionCircuit_selectorActivations_eq_source :
    actionCircuit.selectorActivations = actionSourceSelectorActivations :=
  actionCircuit_selectorActivations_eq_sourceTrace.trans
    (congrArg (fun starts => placeSelectorTrace starts (actionSourceSelectorTrace actionConfig))
      actionCircuit_regionStarts_eq_source)

end Zcash.Snark.ZeroKnowledge
