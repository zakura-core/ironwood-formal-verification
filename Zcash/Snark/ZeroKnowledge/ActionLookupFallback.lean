import Zcash.Snark.ZeroKnowledge.CompiledLookupCompleteness
import Zcash.Snark.ZeroKnowledge.ActionConfiguration
import Zcash.Snark.ZeroKnowledge.CompiledFixedWitnesses

/-!
# The actual Action lookup tables and inactive-row fallbacks

All three configured arguments are identified from the configure program. The
original table loads determine the compiler environment's zero-index generator
entry, which is the tuple selected when the Sinsemilla master is inactive.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark Zcash.Circuits Zcash.Circuits.Action

/-- A loaded original table row is read exactly by the canonical compiler environment. -/
theorem topLevel_loadedTable_value
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) (assignment : ProofAssignment Fp)
    (table : TableColumn) (values : List Fp)
    (hload : Operation.loadTable table values ∈ top.operations)
    (row : ℕ) (hrow : row < values.length) :
    (top.environment assignment).fixed table.inner row = values[row]! := by
  rw [TopLevelCircuit.environment_fixed]
  exact compiledFixedValue_of_mem_raw top (table.inner.index, row, values[row]!)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (FixedLayout.mem_tableAssignments_of_loadTable_of_lt _ _ _ _ hload row hrow))))

/-- Each original generator-table load remains present in the complete post-NU6.3 Action. -/
theorem actionInitialGeneratorLoad_mem (config : Circuit.Config) (region : RegionIndex)
    (operation : Operation Fp)
    (hload : operation ∈ (Sinsemilla.load Specs.Sinsemilla.orchardGenerators
      config.sinsemilla1.generatorTable).operations region) :
    operation ∈ (Circuit.mainPost Specs.Sinsemilla.orchardGenerators orchardBases config ()).operations region := by
  simp only [Circuit.mainPost, Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
  apply List.mem_append_left
  rw [FormalCircuit.call_operations]
  simp only [Circuit.baseCircuit, Circuit.main, CircuitPreNU63.synthesize, Circuit.synthesizeBase,
    Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
  apply List.mem_append_left
  simp only [Circuit.synthWitness, Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
  exact List.mem_append_left _ hload

set_option maxRecDepth 10000 in
/-- The actual configure program supplies precisely these three original lookup arguments. -/
theorem actionCircuit_lookupArguments_eq :
    actionCircuit.constraintSystem.lookups =
      [LookupRangeCheck.rangeCheckLookup 10 actionConfig.lookupConfig,
        Sinsemilla.HashPiece.generatorLookup Specs.Sinsemilla.orchardGenerators actionConfig.sinsemilla1,
        Sinsemilla.HashPiece.generatorLookup Specs.Sinsemilla.orchardGenerators actionConfig.sinsemilla2] := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- The range-check input is zero whenever its master selector is inactive. -/
theorem rangeCheckLookup_inactive (bits : ℕ) (config : LookupRangeCheck.Config bits)
    (valuation : Query → Fp) (hinactive : valuation (.selector config.qLookup) = 0) :
    (LookupRangeCheck.rangeCheckLookup bits config).inputs.map (Expression.eval valuation) = [0] := by
  simp [LookupRangeCheck.rangeCheckLookup, LookupRangeCheck.rangeCheckLookupFor,
    LookupRangeCheck.rangeCheckInputFor, Expression.eval, querySelector, queryAdvice, hinactive]

/-- An inactive Sinsemilla lookup selects the generator indexed by zero. -/
theorem sinsemillaLookup_inactive (generators : Specs.Sinsemilla.Generators)
    (config : Sinsemilla.HashPiece.Config) (valuation : Query → Fp)
    (hinactive : valuation (.selector config.qS1) = 0) :
    (Sinsemilla.HashPiece.generatorLookup generators config).inputs.map (Expression.eval valuation) =
      [0, (generators.S 0).x, (generators.S 0).y] := by
  simp [Sinsemilla.HashPiece.generatorLookup, Expression.eval, querySelector, hinactive]

set_option maxRecDepth 10000 in
/-- The actual compiled table's zero row contains the expected index and generator coordinates. -/
theorem actionCircuit_generatorTable_zero (assignment : ProofAssignment Fp) :
    let table := actionConfig.sinsemilla1.generatorTable
    let environment := actionCircuit.environment assignment
    environment.fixed table.tableIdx.inner 0 = 0 ∧
      environment.fixed table.tableX.inner 0 = (Specs.Sinsemilla.orchardGenerators.S 0).x ∧
      environment.fixed table.tableY.inner 0 = (Specs.Sinsemilla.orchardGenerators.S 0).y := by
  have hloads (operation : Operation Fp)
      (hload : operation ∈ (Sinsemilla.load Specs.Sinsemilla.orchardGenerators
        actionConfig.sinsemilla1.generatorTable).operations 0) : operation ∈ actionCircuit.operations := by
    rw [Internal.actionCircuit_eq_impl]
    exact actionInitialGeneratorLoad_mem actionConfig 0 operation hload
  have hidx := topLevel_loadedTable_value actionCircuit assignment
    actionConfig.sinsemilla1.generatorTable.tableIdx
    ((List.range (2 ^ Specs.K)).map (Nat.cast : ℕ → Fp))
    (hloads _ (by rw [Sinsemilla.load_operations]; simp)) 0 (by simp [Specs.K])
  have hx := topLevel_loadedTable_value actionCircuit assignment
    actionConfig.sinsemilla1.generatorTable.tableX
    ((List.range (2 ^ Specs.K)).map (fun j => (Specs.Sinsemilla.orchardGenerators.S j).x))
    (hloads _ (by rw [Sinsemilla.load_operations]; simp)) 0 (by simp [Specs.K])
  have hy := topLevel_loadedTable_value actionCircuit assignment
    actionConfig.sinsemilla1.generatorTable.tableY
    ((List.range (2 ^ Specs.K)).map (fun j => (Specs.Sinsemilla.orchardGenerators.S j).y))
    (hloads _ (by rw [Sinsemilla.load_operations]; simp)) 0 (by simp [Specs.K])
  simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
    if_pos (by decide : 0 < 2 ^ Specs.K), Option.map_some, Option.getD_some, Nat.cast_zero] using
      And.intro hidx (And.intro hx hy)

end Zcash.Snark.ZeroKnowledge
