import Zcash.Snark.ZeroKnowledge.SelectorActivationTrace
import Clean.Halo2.FormalRegion.ToFormal

/-!
# Selector traces through circuit composition

The normalization rules project operation streams before reducing field values or
witness programs. Child calls remain available as separate proof boundaries, and
loop rules retain their finite iteration structure.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

attribute [selector_trace_norm]
  regionSelectorTrace_nil regionSelectorTrace_cons regionSelectorTrace_append regionSelectorTrace_flatMap
  regionSelectorTrace_enableGate regionSelectorTrace_enableLookup
  regionSelectorTrace_assignAdvice regionSelectorTrace_assignFixed
  regionSelectorTrace_constrainEqual regionSelectorTrace_constrainConstant
  regionSelectorTrace_constrainInstance
  selectorTrace_nil selectorTrace_cons selectorTrace_append selectorTrace_flatMap
  selectorTrace_region selectorTrace_constrainInstance selectorTrace_loadTable
  RegionCircuit.operations_bind RegionCircuit.operations_pure
  Circuit.operations_bind Circuit.operations_pure
  operations_assignRegion operations_assignAdvice operations_assignFixed
  operations_copyAdvice operations_enable operations_enableLookup
  operations_constrainEqual operations_constrainInstance operations_loadTable
  operations_constrainConstant operations_assignAdviceFromInstance
  operations_cellAt operations_cellVec
  List.append_nil List.nil_append

variable {F α β : Type}

@[selector_trace_norm]
theorem regionSelectorTrace_flatten (bodies : List (RegionOperations F)) :
    regionSelectorTrace bodies.flatten = (bodies.map regionSelectorTrace).flatten := by
  simp only [List.flatten_eq_flatMap, regionSelectorTrace_flatMap, List.flatMap_map]
  rfl

@[selector_trace_norm]
theorem selectorTrace_flatten (bodies : List (Operations F)) :
    selectorTrace bodies.flatten = (bodies.map selectorTrace).flatten := by
  simp only [List.flatten_eq_flatMap, selectorTrace_flatMap, List.flatMap_map]
  rfl

variable [FiniteField F]

/-- A fixed-stride loop exposes only its per-iteration selector traces. -/
@[selector_trace_norm]
theorem regionSelectorTrace_forRange' (offset stride count : ℕ)
    (body : ℕ → ℕ → RegionCircuit F Unit) (region : RegionIndex) :
    regionSelectorTrace ((RegionCircuit.forRange' offset stride count body).operations region) =
      (List.ofFn fun i : Fin count =>
        regionSelectorTrace ((body i.val (offset + i.val * stride)).operations region)).flatten := by
  rw [RegionCircuit.forRange'_operations, regionSelectorTrace_flatten, List.map_ofFn]
  rfl

/-- Variable row schedules keep the same trace projection. -/
@[selector_trace_norm]
theorem regionSelectorTrace_forRangeVar' (rows : ℕ → ℕ) (count : ℕ)
    (body : ℕ → ℕ → RegionCircuit F Unit) (region : RegionIndex) :
    regionSelectorTrace ((RegionCircuit.forRangeVar' rows count body).operations region) =
      (List.ofFn fun i : Fin count =>
        regionSelectorTrace ((body i.val (rows i.val)).operations region)).flatten := by
  rw [RegionCircuit.forRangeVar'_operations, regionSelectorTrace_flatten, List.map_ofFn]
  rfl

/-- Accumulator-dependent folds preserve every activation of each actual iteration. -/
@[selector_trace_norm]
theorem regionSelectorTrace_foldRange (offset stride count : ℕ) (initial : β)
    (body : ℕ → ℕ → β → RegionCircuit F β) (region : RegionIndex) :
    regionSelectorTrace ((RegionCircuit.foldRange offset stride count initial body).operations region) =
      (List.ofFn fun i : Fin count =>
        regionSelectorTrace ((body i.val (offset + i.val * stride)
          (RegionCircuit.foldAcc (fun j => offset + j * stride) initial body i.val region)).operations region)).flatten := by
  unfold RegionCircuit.foldRange RegionCircuit.foldRangeVar
  rw [RegionCircuit.foldRangeVarAux_operations, regionSelectorTrace_flatten, List.map_ofFn]
  rfl

/-- Promoting a region gadget to a layouter gadget contributes exactly one region,
including when that region's selector trace is empty. -/
@[selector_trace_norm]
theorem selectorTrace_toFormal_call {ConfigInput Config : Type}
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F) (region : RegionIndex) :
    selectorTrace (((child.toFormal name).call config input).operations region) =
      [regionSelectorTrace ((child.call config 0 input).operations region)] := by
  rw [FormalCircuit.call_operations, FormalRegionCircuit.call_operations]
  rfl

end Zcash.Snark.ZeroKnowledge
