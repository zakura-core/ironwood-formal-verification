import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Circuits.Poseidon.Hash

/-!
# Exact selector trace of the Action Poseidon hash

The trace keeps the initial empty region, the input gate at row one, and the
4/28/4 full/partial/full permutation schedule. Round constants and private state
values do not enter the resulting trace.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- A full Poseidon round records its full-round selector, supplying the source metadata for Action
selector coverage. -/
@[selector_trace_norm]
theorem poseidonFullRound_regionSelectorTrace (round : ℕ) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((Poseidon.fullRound round).call config offset input).operations region) =
      [(config.sFull.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- A partial Poseidon round records its partial-round selector, supplying the source metadata for
Action selector coverage. -/
@[selector_trace_norm]
theorem poseidonPartialRound_regionSelectorTrace (round : ℕ) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((Poseidon.partialRound round).call config offset input).operations region) =
      [(config.sPartial.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- The exact gate-row schedule of the width-three permutation. -/
def poseidonPermutationSelectorTrace (config : Poseidon.Config) (offset : ℕ) : List (ℕ × ℕ) :=
  selectorRowRun config.sFull.index offset 4 ++
    selectorRowRun config.sPartial.index (offset + 4) 28 ++
    selectorRowRun config.sFull.index (offset + 32) 4

/-- The Poseidon permutation retains the full and partial round schedule, supplying the source
metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem poseidonPermutation_regionSelectorTrace (config : Poseidon.Config) (offset : ℕ)
    (input : Var Poseidon.Permute.State Fp) (region : RegionIndex) :
    regionSelectorTrace ((Poseidon.permuteRegion.call config offset input).operations region) =
      poseidonPermutationSelectorTrace config offset := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((Poseidon.permuteSynthesize config offset input).operations region) = _
  simp only [Poseidon.permuteSynthesize, selector_trace_norm,
    selectorRowRun, poseidonPermutationSelectorTrace, Nat.mul_one, List.append_assoc]
  rw [Poseidon.operations_readStateRow]
  simp only [regionSelectorTrace_nil, List.append_nil]

/-- Poseidon initialization adds no selector activations, so trace extraction can omit its field
assignments. -/
@[selector_trace_norm]
theorem poseidonInit_regionSelectorTrace (capacity : Fp) (config : Poseidon.Config)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((Poseidon.initRegion capacity).call config offset input).operations region) = [] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Poseidon input absorption retains its configured activation trace, supplying the source metadata
for Action selector coverage. -/
@[selector_trace_norm]
theorem poseidonInput_regionSelectorTrace (config : Poseidon.Config) (offset : ℕ)
    (input : Var Poseidon.Sponge.AddInputInput Fp) (region : RegionIndex) :
    regionSelectorTrace ((Poseidon.addInputRegion.call config offset input).operations region) =
      [(config.sPadAndAdd.index, offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- All three regions of the actual constant-length hash circuit. -/
@[selector_trace_norm]
theorem poseidonHash_selectorTrace (capacity : Fp) (config : Poseidon.Config)
    (input : Var Poseidon.Sponge.Rate2 Fp) (region : RegionIndex) :
    selectorTrace (((Poseidon.hash capacity).call config input).operations region) =
      [[], [(config.sPadAndAdd.index, 1)], poseidonPermutationSelectorTrace config 0] := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((Poseidon.synthesize capacity config input).operations region) = _
  simp only [Poseidon.synthesize, selector_trace_norm, List.cons_append]

end Zcash.Snark.ZeroKnowledge
