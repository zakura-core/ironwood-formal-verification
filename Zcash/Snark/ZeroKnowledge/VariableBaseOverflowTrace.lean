import Zcash.Snark.ZeroKnowledge.VariableBaseSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace

/-!
# Complete variable-base multiplication selector trace

This joins the main region to the three overflow-check regions, keeping the empty
scalar-loading region and the running-sum lookup activations in their source order.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

@[selector_trace_norm]
theorem overflowGate_regionSelectorTrace (K : ℕ) (config : Ecc.MulOverflow.Config K)
    (input : Var Ecc.MulOverflow.Inputs Fp) (scalar low : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulOverflow.gateRegion K config input scalar low).operations region) =
      [(config.qOverflow.index, 1)] := rfl

@[selector_trace_norm]
theorem overflow_selectorTrace (K : ℕ) (hKW : K * Ecc.MulOverflow.numWords K = 130)
    (config : Ecc.MulOverflow.Config K) (input : Var Ecc.MulOverflow.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((Ecc.MulOverflow.circuit K hKW).call config input).operations region) =
      [[], runningSelectorTrace config.lookupConfig 0 (Ecc.MulOverflow.numWords K),
        [(config.qOverflow.index, 1)]] := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((Ecc.MulOverflow.synthesize K config input).operations region) = _
  simp only [Ecc.MulOverflow.synthesize, selector_trace_norm, List.cons_append]

/-- All four regions of the actual variable-base multiplication gadget. -/
def variableBaseSelectorTrace (config : Ecc.Mul.Config) : List (List (ℕ × ℕ)) :=
  [variableBaseMainSelectorTrace config, [],
    runningSelectorTrace config.overflowConfig.lookupConfig 0 13,
    [(config.overflowConfig.qOverflow.index, 1)]]

@[selector_trace_norm]
theorem variableBase_selectorTrace (config : Ecc.Mul.Config)
    (input : Var Ecc.Mul.Inputs Fp) (region : RegionIndex) :
    selectorTrace ((Ecc.Mul.mul.call config input).operations region) =
      variableBaseSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((Ecc.Mul.synthesize config input).operations region) = _
  simp only [Ecc.Mul.synthesize, selector_trace_norm, variableBaseSelectorTrace,
    Ecc.MulOverflow.numWords, List.cons_append]

end Zcash.Snark.ZeroKnowledge
