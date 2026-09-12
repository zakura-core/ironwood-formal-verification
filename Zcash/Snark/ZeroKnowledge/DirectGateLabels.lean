import Zcash.Snark.ZeroKnowledge.GateActivationCoverage

/-!# Direct projection of original gate activation metadata
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark

/-- Reflect only the source metadata needed by coverage, without constructing intermediate gate records. -/
def regionSourceGateLabels {F : Type} (place : RegionIndex → ℕ) (region : RegionIndex) :
    RegionOperations F → List (ℕ × String × ℕ)
  | [] => []
  | .enableGate gate row :: rest =>
    (gate.selector.index, gate.name, place region + row) :: regionSourceGateLabels place region rest
  | _ :: rest => regionSourceGateLabels place region rest

/-- The direct projection retains the original region-counter threading. -/
def operationSourceGateLabels {F : Type} (place : RegionIndex → ℕ) :
    Operations F → RegionIndex → List (ℕ × String × ℕ)
  | [], _ => []
  | .region _ body :: rest, region =>
    regionSourceGateLabels place region body ++ operationSourceGateLabels place rest (region + 1)
  | _ :: rest, region => operationSourceGateLabels place rest region

/-- Direct region metadata are exactly the labels of the original enabled-gate records. -/
theorem regionSourceGateLabels_eq {F : Type} (place : RegionIndex → ℕ)
    (region : RegionIndex) (body : RegionOperations F) :
    regionSourceGateLabels place region body =
      (regionEnabledGates region body).map (fun enabled =>
        (enabled.gate.selector.index, enabled.gate.name, place enabled.region + enabled.row)) := by
  induction body with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;> simp only [regionSourceGateLabels, regionEnabledGates, List.map_cons, ih]

/-- Direct reflection is extensionally equal to the original complete gate schedule. -/
theorem operationSourceGateLabels_eq {F : Type} (place : RegionIndex → ℕ)
    (operations : Operations F) (initial : RegionIndex) :
    operationSourceGateLabels place operations initial = sourceGateActivationLabels place operations initial := by
  unfold sourceGateActivationLabels
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;> simp only [operationSourceGateLabels, operationEnabledGates,
      List.map_append, regionSourceGateLabels_eq, ih]

end Zcash.Snark.ZeroKnowledge
