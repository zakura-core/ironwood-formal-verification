import Zcash.Circuits.Integration.TopLevelCoherence
import Std.Data.HashSet.Lemmas
import Mathlib.Data.List.Nodup

/-!
# Coverage of source gates sharing compiled selectors

A selector can guard more than one configured gate. The finite coverage check
retains both the gate name and row, and its soundness theorem recovers the
original registered gate at every activated row.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2
open Zcash.Snark

/-- Source identity used only after injectivity has been checked against the configured gates. -/
def sourceGateLabel {F : Type} (gate : Gate F) : ℕ × String :=
  (gate.selector.index, gate.name)

/-- Every original gate activation, retaining its full source label and placed row. -/
def sourceGateActivationLabels {F : Type} (place : RegionIndex → ℕ)
    (operations : Operations F) (initial : RegionIndex) : List (ℕ × String × ℕ) :=
  (operationEnabledGates operations initial).map fun enabled =>
    (enabled.gate.selector.index, enabled.gate.name, place enabled.region + enabled.row)

/-- Require every gate sharing an activated selector to appear at that exact row. -/
def gateActivationCoverageCheck (gates : List (ℕ × String))
    (activations : List (ℕ × ℕ)) (labels : List (ℕ × String × ℕ)) : Bool :=
  let emitted := Std.HashSet.ofList labels
  gates.all fun gate => activations.all fun activation =>
    gate.1 != activation.1 || emitted.contains (gate.1, gate.2, activation.2)

/-- A successful finite coverage check retains the particular gate name at every activated row. -/
theorem gateActivationCoverageCheck_sound (gates : List (ℕ × String))
    (activations : List (ℕ × ℕ)) (labels : List (ℕ × String × ℕ))
    (hcheck : gateActivationCoverageCheck gates activations labels = true)
    (gate : ℕ × String) (hgate : gate ∈ gates) (row : ℕ)
    (hrow : (gate.1, row) ∈ activations) :
    (gate.1, gate.2, row) ∈ labels := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp hcheck gate hgate) (gate.1, row) hrow
  simpa only [bne_self_eq_false, Bool.false_or, Std.HashSet.contains_ofList,
    List.contains_iff_mem] using h

/-- Labels recover actual registered gates once configured label injectivity is checked. -/
theorem topLevel_gate_enabled_of_coverage {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)
    (hlabels : (top.constraintSystem.gates.map sourceGateLabel).Nodup)
    (hcoverage : gateActivationCoverageCheck (top.constraintSystem.gates.map sourceGateLabel)
      top.selectorActivations (sourceGateActivationLabels top.placement top.operations 0) = true)
    (gate : Gate F) (hgate : gate ∈ top.constraintSystem.gates)
    (row : ℕ) (hrow : (gate.selector.index, row) ∈ top.selectorActivations) :
    ∃ enabled ∈ operationEnabledGates top.operations 0,
      enabled.gate = gate ∧ top.placement enabled.region + enabled.row = row := by
  have hlabel := gateActivationCoverageCheck_sound _ _ _ hcoverage (sourceGateLabel gate)
    (List.mem_map_of_mem hgate) row hrow
  obtain ⟨enabled, henabled, hequal⟩ := List.mem_map.mp hlabel
  have hregistered := OperationsKeygenCoherent.gate top.keygenCoherent henabled
  have hgateLabel : sourceGateLabel enabled.gate = sourceGateLabel gate := by
    have hindex : enabled.gate.selector.index = gate.selector.index :=
      congrArg (fun value : ℕ × String × ℕ => value.1) hequal
    have hname : enabled.gate.name = gate.name :=
      congrArg (fun value : ℕ × String × ℕ => value.2.1) hequal
    exact Prod.ext hindex hname
  have hgateEq : enabled.gate = gate :=
    List.inj_on_of_nodup_map hlabels hregistered hgate hgateLabel
  exact ⟨enabled, henabled, hgateEq, congrArg (fun value => value.2.2) hequal⟩

end Zcash.Snark.ZeroKnowledge
