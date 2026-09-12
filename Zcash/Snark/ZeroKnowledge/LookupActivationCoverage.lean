import Zcash.Snark.ZeroKnowledge.GateActivationCoverage
import Zcash.Circuits.Integration.OperationLookups

/-!
# Exact source lookup activation metadata and coverage
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark

/-- The original lookup's master index and exact placed activation row. -/
def sourceLookupActivationLabels {F : Type} (place : RegionIndex → ℕ)
    (operations : Operations F) (initial : RegionIndex) : List (ℕ × ℕ) :=
  (operationEnabledLookups operations initial).map fun lookup =>
    (lookup.argument.masterSelector.index, place lookup.region + lookup.row)

/-- Direct source projection without constructing intermediate enabled-lookup records. -/
def regionSourceLookupLabels {F : Type} (place : RegionIndex → ℕ) (region : RegionIndex) :
    RegionOperations F → List (ℕ × ℕ)
  | [] => []
  | .enableLookup argument _ row :: rest =>
    (argument.masterSelector.index, place region + row) :: regionSourceLookupLabels place region rest
  | _ :: rest => regionSourceLookupLabels place region rest

/-- The original operation walk, retaining region-counter threading. -/
def operationSourceLookupLabels {F : Type} (place : RegionIndex → ℕ) :
    Operations F → RegionIndex → List (ℕ × ℕ)
  | [], _ => []
  | .region _ body :: rest, region =>
    regionSourceLookupLabels place region body ++ operationSourceLookupLabels place rest (region + 1)
  | _ :: rest, region => operationSourceLookupLabels place rest region

/-- Direct metadata preserve each original lookup activation in a region. -/
theorem regionSourceLookupLabels_eq {F : Type} (place : RegionIndex → ℕ)
    (region : RegionIndex) (body : RegionOperations F) :
    regionSourceLookupLabels place region body =
      (regionEnabledLookups region body).map (fun lookup =>
        (lookup.argument.masterSelector.index, place lookup.region + lookup.row)) := by
  induction body with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;> simp only [regionSourceLookupLabels, regionEnabledLookups, List.map_cons, ih]

/-- Direct reflection retains the exact complete original lookup schedule. -/
theorem operationSourceLookupLabels_eq {F : Type} (place : RegionIndex → ℕ)
    (operations : Operations F) (initial : RegionIndex) :
    operationSourceLookupLabels place operations initial = sourceLookupActivationLabels place operations initial := by
  unfold sourceLookupActivationLabels
  induction operations generalizing initial with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;> simp only [operationSourceLookupLabels, operationEnabledLookups,
      List.map_append, regionSourceLookupLabels_eq, ih]

/-- Every active configured lookup master must name an original lookup activation. -/
def lookupActivationCoverageCheck (masters : List ℕ)
    (activations labels : List (ℕ × ℕ)) : Bool :=
  let emitted := Std.HashSet.ofList labels
  masters.all fun master => activations.all fun activation =>
    master != activation.1 || emitted.contains (master, activation.2)

/-- A successful scan retains the specific lookup master at every activated row. -/
theorem lookupActivationCoverageCheck_sound (masters : List ℕ) (activations labels : List (ℕ × ℕ))
    (hcheck : lookupActivationCoverageCheck masters activations labels = true)
    (master : ℕ) (hmaster : master ∈ masters) (row : ℕ) (hrow : (master, row) ∈ activations) :
    (master, row) ∈ labels := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp hcheck master hmaster) (master, row) hrow
  simpa only [bne_self_eq_false, Bool.false_or, Std.HashSet.contains_ofList,
    List.contains_iff_mem] using h

/-- Checked coverage recovers the actual lookup even when a gate shares its master selector. -/
theorem topLevel_lookup_enabled_of_coverage {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)
    (hmasters : (top.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index)).Nodup)
    (hcoverage : lookupActivationCoverageCheck (top.constraintSystem.lookups.map (fun lookup => lookup.masterSelector.index))
      top.selectorActivations (sourceLookupActivationLabels top.placement top.operations 0) = true)
    (argument : LookupArgument F) (hargument : argument ∈ top.constraintSystem.lookups)
    (row : ℕ) (hrow : (argument.masterSelector.index, row) ∈ top.selectorActivations) :
    ∃ lookup ∈ operationEnabledLookups top.operations 0,
      lookup.argument = argument ∧ top.placement lookup.region + lookup.row = row := by
  have hlabel := lookupActivationCoverageCheck_sound _ _ _ hcoverage argument.masterSelector.index
    (List.mem_map_of_mem hargument) row hrow
  obtain ⟨lookup, hlookup, hequal⟩ := List.mem_map.mp hlabel
  have hregistered := OperationsKeygenCoherent.lookup top.keygenCoherent hlookup
  have hargumentEq : lookup.argument = argument := List.inj_on_of_nodup_map hmasters
    hregistered hargument (congrArg Prod.fst hequal)
  exact ⟨lookup, hlookup, hargumentEq, congrArg Prod.snd hequal⟩

end Zcash.Snark.ZeroKnowledge
