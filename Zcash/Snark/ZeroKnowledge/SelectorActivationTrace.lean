import Clean.Halo2.Formal.Call
import Clean.Halo2.FormalRegion.Call
import Clean.Halo2.Keygen.FloorPlanner.RegionShape

/-!
# Compositional selector-activation traces

These projections discard witness computations and keep every selector activation,
its local row, and its region's position in the synthesis stream. Empty regions
remain in the trace because they still advance the floor planner's region index.
`activations_eq_placeSelectorTrace` connects this smaller representation to the
compiler's actual activation walk, for any supplied placement.
-/

register_simp_attr selector_trace_norm

namespace Zcash.Snark.ZeroKnowledge

open Halo2

variable {F : Type}

/-- A region's ordered selector activations, before floor-planner placement. -/
def regionSelectorTrace (body : RegionOperations F) : List (ℕ × ℕ) :=
  body.flatMap fun operation => match operation with
    | .enableGate gate row => [(gate.selector.index, row)]
    | .enableLookup _ enabled row => enabled.map fun selector => (selector.index, row)
    | _ => []

/-- The ordered region traces; even a region with no selectors occupies one slot. -/
def selectorTrace (operations : Operations F) : List (List (ℕ × ℕ)) :=
  operations.filterMap fun operation => match operation with
    | .region _ body => some (regionSelectorTrace body)
    | _ => none

/-- Apply the compiler's region starts to a compact selector trace. -/
def placeSelectorTrace (starts : List ℕ) (trace : List (List (ℕ × ℕ)))
    (initial : ℕ := 0) : List (ℕ × ℕ) :=
  (trace.zipIdx initial).flatMap fun (body, index) =>
    body.map fun (selector, row) => (selector, starts.getD index 0 + row)

theorem regionSelectorTrace_nil : regionSelectorTrace ([] : RegionOperations F) = [] := rfl

theorem regionSelectorTrace_cons (operation : RegionOperation F) (rest : RegionOperations F) :
    regionSelectorTrace (operation :: rest) =
      (match operation with
        | .enableGate gate row => [(gate.selector.index, row)]
        | .enableLookup _ enabled row => enabled.map fun selector => (selector.index, row)
        | _ => []) ++ regionSelectorTrace rest := rfl

theorem regionSelectorTrace_append (left right : RegionOperations F) :
    regionSelectorTrace (left ++ right) = regionSelectorTrace left ++ regionSelectorTrace right := by
  simp only [regionSelectorTrace, List.flatMap_append]

theorem regionSelectorTrace_flatMap {α : Type} (items : List α)
    (body : α → RegionOperations F) :
    regionSelectorTrace (items.flatMap body) = items.flatMap (fun item => regionSelectorTrace (body item)) := by
  simp only [regionSelectorTrace, List.flatMap_assoc]

theorem regionSelectorTrace_enableGate (gate : Gate F) (row : ℕ) :
    regionSelectorTrace [.enableGate gate row] = [(gate.selector.index, row)] := rfl

theorem regionSelectorTrace_enableLookup (argument : LookupArgument F)
    (enabled : List Selector) (row : ℕ) :
    regionSelectorTrace [.enableLookup argument enabled row] =
      enabled.map (fun selector => (selector.index, row)) := by
  simp only [regionSelectorTrace, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem regionSelectorTrace_assignAdvice (column : Column .advice) (witness : WitgenIR F 1) (row : ℕ) :
    regionSelectorTrace [.assignAdvice column row witness] = [] := rfl

theorem regionSelectorTrace_assignFixed (column : Column .fixed) (row : ℕ) (value : F) :
    regionSelectorTrace [.assignFixed column row value] = [] := rfl

theorem regionSelectorTrace_constrainEqual (left right : Cell) :
    regionSelectorTrace [.constrainEqual left right] (F := F) = [] := rfl

theorem regionSelectorTrace_constrainConstant (cell : Cell) (value : F) :
    regionSelectorTrace [.constrainConstant cell value] = [] := rfl

theorem regionSelectorTrace_constrainInstance (cell : Cell) (column : Column .instance) (row : ℕ) :
    regionSelectorTrace [.constrainInstance cell column row] (F := F) = [] := rfl

theorem selectorTrace_nil : selectorTrace ([] : Operations F) = [] := rfl

theorem selectorTrace_cons (operation : Operation F) (rest : Operations F) :
    selectorTrace (operation :: rest) = match operation with
      | .region _ body => regionSelectorTrace body :: selectorTrace rest
      | _ => selectorTrace rest := by
  cases operation <;> rfl

theorem selectorTrace_append (left right : Operations F) :
    selectorTrace (left ++ right) = selectorTrace left ++ selectorTrace right := by
  simp only [selectorTrace, List.filterMap_append]

theorem selectorTrace_flatMap {α : Type} (items : List α) (body : α → Operations F) :
    selectorTrace (items.flatMap body) = items.flatMap (fun item => selectorTrace (body item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, selectorTrace_append, ih]

theorem selectorTrace_region (name : String) (body : RegionOperations F) :
    selectorTrace [.region name body] = [regionSelectorTrace body] := rfl

theorem selectorTrace_constrainInstance (cell : Cell) (column : Column .instance) (row : ℕ) :
    selectorTrace [.constrainInstance cell column row] (F := F) = [] := rfl

theorem selectorTrace_loadTable (table : TableColumn) (values : List F) :
    selectorTrace [.loadTable table values] = [] := rfl

/-- Compact trace placement is exactly the compiler's activation walk, including
region-index advancement through empty traces and ignored non-region operations. -/
theorem activations_eq_placeSelectorTrace (starts : List ℕ) (operations : Operations F) (initial : ℕ) :
    activations starts (indexedRegions operations initial).1 =
      placeSelectorTrace starts (selectorTrace operations) initial := by
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [indexedRegions, activations, List.flatMap_cons,
            selectorTrace, List.filterMap_cons, placeSelectorTrace, List.zipIdx_cons,
            List.map_flatMap, regionSelectorTrace] at ih ⊢
          rw [ih]
          congr 1
          apply List.flatMap_congr
          intro operation hoperation
          cases operation <;> simp
      | constrainInstance cell column row => exact ih initial
      | loadTable table values => exact ih initial

end Zcash.Snark.ZeroKnowledge
