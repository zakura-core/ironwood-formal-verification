import Zcash.Snark.ZeroKnowledge.FixedBaseVariantTrace
import Zcash.Snark.ZeroKnowledge.VariableBaseOverflowTrace
import Zcash.Snark.ZeroKnowledge.PoseidonSelectorTrace

/-!
# Selector traces of Action's auxiliary checks

These source equations compose the scalar-multiplication and Poseidon traces for
value commitments, spend authority, address integrity, and nullifier derivation.
Every empty region and final addition remains in the resulting region sequence.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

@[selector_trace_norm]
theorem addChip_regionSelectorTrace (config : AddChip.Config) (offset : ℕ)
    (input : Var AddChip.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace ((AddChip.add.call config offset input).operations region) =
      [(config.qAdd.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- The five-region value-commitment trace. -/
def valueCommitSelectorTrace
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    List (List (ℕ × ℕ)) :=
  [runningFixedInnerSelectorTrace config.1.superConfig 0 22,
    [(config.1.superConfig.addConfig.qAdd.index, 0), (config.1.qMulFixedShort.index, 1)],
    fullWidthInnerSelectorTrace config.2.1 0, [(config.2.1.superConfig.addConfig.qAdd.index, 0)],
    [(config.2.2.qAdd.index, 0)]]

@[selector_trace_norm]
theorem valueCommit_selectorTrace (valueBase : Ecc.MulFixed.Short.FixedBase) (blindBase : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Action.ValueCommit.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((Action.ValueCommit.circuit valueBase blindBase).call config input).operations region) =
      valueCommitSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  simp only [Action.ValueCommit.circuit, Ecc.Add.addFormal, selector_trace_norm,
    valueCommitSelectorTrace, List.cons_append]

/-- The three-region spend-authority trace. -/
def spendAuthoritySelectorTrace (config : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config) :
    List (List (ℕ × ℕ)) :=
  [fullWidthInnerSelectorTrace config.1 0, [(config.1.superConfig.addConfig.qAdd.index, 0)],
    [(config.2.qAdd.index, 0)]]

@[selector_trace_norm]
theorem spendAuthority_selectorTrace (base : Ecc.MulFixed.FixedBase)
    (config : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var Action.SpendAuthority.Input Fp) (region : RegionIndex) :
    selectorTrace (((Action.SpendAuthority.circuit base).call config input).operations region) =
      spendAuthoritySelectorTrace config := by
  rw [FormalCircuit.call_operations]
  simp only [Action.SpendAuthority.circuit, Ecc.Add.addFormal, selector_trace_norm,
    spendAuthoritySelectorTrace, List.cons_append]

/-- Address integrity retains the point-witness region and the final selector-free copy region. -/
def addressIntegritySelectorTrace (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config) :
    List (List (ℕ × ℕ)) :=
  variableBaseSelectorTrace config.1 ++ [[(config.2.qPointNonId.index, 0)], []]

@[selector_trace_norm]
theorem addressIntegrity_selectorTrace (config : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (input : Var Action.AddressIntegrity.Input Fp) (region : RegionIndex) :
    selectorTrace ((Action.AddressIntegrity.circuit.call config input).operations region) =
      addressIntegritySelectorTrace config := by
  rw [FormalCircuit.call_operations]
  simp only [Action.AddressIntegrity.circuit, Ecc.WitnessPoint.pointNonIdFormal,
    selector_trace_norm, addressIntegritySelectorTrace, List.cons_append]

/-- The nine-region nullifier trace, including the Poseidon permutation schedule. -/
def nullifierSelectorTrace
    (config : Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config) :
    List (List (ℕ × ℕ)) :=
  [[], [(config.1.sPadAndAdd.index, 1)], poseidonPermutationSelectorTrace config.1 0,
    [(config.2.1.qAdd.index, 0)], runningFixedInnerSelectorTrace config.2.2.1.superConfig 0 85,
    [(config.2.2.1.superConfig.addConfig.qAdd.index, 0)], runningSelectorTrace config.2.2.1.lookupConfig 0 13,
    [(config.2.2.1.qMulFixedBaseField.index, 1)], [(config.2.2.2.qAdd.index, 0)]]

@[selector_trace_norm]
theorem nullifier_selectorTrace (base : Ecc.MulFixed.FixedBase)
    (config : Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config)
    (input : Var Action.DeriveNullifier.Input Fp) (region : RegionIndex) :
    selectorTrace (((Action.DeriveNullifier.circuit base).call config input).operations region) =
      nullifierSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((Action.DeriveNullifier.synthesize base config input).operations region) = _
  simp only [Action.DeriveNullifier.synthesize, AddChip.addFormal, Ecc.Add.addFormal,
    selector_trace_norm, nullifierSelectorTrace, List.cons_append]

end Zcash.Snark.ZeroKnowledge
