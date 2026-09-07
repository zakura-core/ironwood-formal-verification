import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Circuits.Action.Circuit

/-!
# Source-derived selector traces for Action witness loading

These equations retain the source circuit's selector indices and local rows, for
arbitrary witness programs, input cells, and ambient region indices.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

@[selector_trace_norm]
theorem witnessPoint_regionSelectorTrace (config : Ecc.WitnessPoint.Config) (offset : ℕ)
    (input : Var (Unconstrained Point) Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.WitnessPoint.point.call config offset input).operations region) =
      [(config.qPoint.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem witnessNonIdPoint_regionSelectorTrace (config : Ecc.WitnessPoint.Config) (offset : ℕ)
    (input : Var (Unconstrained Point) Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.WitnessPoint.pointNonId.call config offset input).operations region) =
      [(config.qPointNonId.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem completeAdd_regionSelectorTrace (config : Ecc.Add.Config) (offset : ℕ)
    (input : Var Ecc.Add.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.Add.add.call config offset input).operations region) =
      [(config.qAdd.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem sinsemillaLoad_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (table : Sinsemilla.GeneratorTableConfig) (region : RegionIndex) :
    selectorTrace ((Sinsemilla.load generators table).operations region) = [] := rfl

@[selector_trace_norm]
theorem loadPrivate_selectorTrace (column : Column .advice) (witness : WitgenIR Fp 1)
    (region : RegionIndex) :
    selectorTrace ((Action.Circuit.loadPrivate column witness).operations region) = [[]] := rfl

/-- All eight witness-loading regions, including the five regions with no selectors. -/
@[selector_trace_norm]
theorem actionSynthWitness_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (witness : Action.Circuit.Witnesses Fp) (config : Action.Circuit.Config) (region : RegionIndex) :
    selectorTrace ((Action.Circuit.synthWitness generators witness config).operations region) =
      [[], [], [(config.eccConfig.witnessPoint.qPoint.index, 0)],
        [(config.eccConfig.witnessPoint.qPointNonId.index, 0)],
        [(config.eccConfig.witnessPoint.qPointNonId.index, 0)], [], [], []] := by
  simp only [Action.Circuit.synthWitness, Ecc.WitnessPoint.pointFormal,
    Ecc.WitnessPoint.pointNonIdFormal, selector_trace_norm, List.cons_append]

end Zcash.Snark.ZeroKnowledge
