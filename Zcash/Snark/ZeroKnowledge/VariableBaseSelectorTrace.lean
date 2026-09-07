import Zcash.Snark.ZeroKnowledge.ActionWitnessSelectorTrace

/-!
# Selector traces of variable-base scalar multiplication

The incomplete and complete rounds expose their exact activation offsets without
expanding the scalar witness or the intermediate elliptic-curve points.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- Interior incomplete-addition gates occur one row after their round starts. -/
def incompleteRoundsSelectorTrace (config : Ecc.MulIncomplete.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count => [(config.qMul2.index, offset + i.val + 1)]).flatten

/-- Initial, interior, and final incomplete-addition selectors in source order. -/
def incompleteSelectorTrace (config : Ecc.MulIncomplete.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  [(config.qMul1.index, offset)] ++ incompleteRoundsSelectorTrace config offset count ++
    [(config.qMul3.index, offset + count + 1)]

@[selector_trace_norm]
theorem incompleteRound_regionSelectorTrace (bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var (Unconstrained field) Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulIncomplete.round bit).call config offset input).operations region) =
      [(config.qMul2.index, offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem incompleteLoop_regionSelectorTrace (count bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var (Unconstrained field) Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulIncomplete.loop count bit).call config offset input).operations region) =
      incompleteRoundsSelectorTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((Ecc.MulIncomplete.loopProgram count bit config offset input).operations region) = _
  rw [Ecc.MulIncomplete.loopProgram_operations]
  simp only [selector_trace_norm, Nat.mul_one, incompleteRoundsSelectorTrace]

@[selector_trace_norm]
theorem incomplete_regionSelectorTrace (count bit : ℕ) (config : Ecc.MulIncomplete.Config)
    (offset : ℕ) (input : Var Ecc.MulIncomplete.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulIncomplete.double_and_add count bit).call config offset input).operations region) =
      incompleteSelectorTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Ecc.MulIncomplete.double_and_add, selector_trace_norm,
    Ecc.MulIncomplete.operations_readState, Ecc.MulIncomplete.qMul1Gate_selector,
    Ecc.MulIncomplete.qMul3Gate_selector, incompleteSelectorTrace, List.append_assoc]

/-- The decomposition selector and the two complete-addition selectors in each bit round. -/
def completeRoundsSelectorTrace (config : Ecc.MulComplete.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count =>
    [(config.qDecompose.index, offset + i.val * 2 + 1),
      (config.addConfig.qAdd.index, offset + i.val * 2),
      (config.addConfig.qAdd.index, offset + i.val * 2 + 1)]).flatten

@[selector_trace_norm]
theorem completeRound_regionSelectorTrace (bit iteration : ℕ) (config : Ecc.MulComplete.Config)
    (offset : ℕ) (input : Var Ecc.MulComplete.RoundInputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulComplete.round bit iteration).call config offset input).operations region) =
      [(config.qDecompose.index, offset + 1), (config.addConfig.qAdd.index, offset),
        (config.addConfig.qAdd.index, offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((Ecc.MulComplete.roundSynthesize bit iteration config offset input).operations region) = _
  simp only [Ecc.MulComplete.roundSynthesize, selector_trace_norm,
    Ecc.MulComplete.decomposeGate_selector, List.cons_append]

@[selector_trace_norm]
theorem completeStartCopy_regionSelectorTrace (config : Ecc.MulComplete.Config)
    (input : Var Ecc.MulComplete.Inputs Fp) (offset : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulComplete.startCopy config input offset).operations region) = [] := rfl

@[selector_trace_norm]
theorem complete_regionSelectorTrace (count bit : ℕ) (config : Ecc.MulComplete.Config)
    (offset : ℕ) (input : Var Ecc.MulComplete.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((Ecc.MulComplete.assign_region count bit).call config offset input).operations region) =
      completeRoundsSelectorTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((Ecc.MulComplete.assignRegionSynthesize count bit config offset input).operations region) = _
  simp only [Ecc.MulComplete.assignRegionSynthesize, selector_trace_norm,
    Ecc.MulComplete.operations_zsCells, completeRoundsSelectorTrace]

/-- Every selector activation in the actual variable-base multiplication main region. -/
def variableBaseMainSelectorTrace (config : Ecc.Mul.Config) : List (ℕ × ℕ) :=
  [(config.addConfig.qAdd.index, 0)] ++
    incompleteSelectorTrace config.hiConfig 1 124 ++
    incompleteSelectorTrace config.loConfig 1 125 ++
    completeRoundsSelectorTrace config.completeConfig 129 3 ++
    [(config.qMulLsb.index, 135), (config.addConfig.qAdd.index, 135)]

@[selector_trace_norm]
theorem variableBaseMain_regionSelectorTrace (config : Ecc.Mul.Config)
    (offset : ℕ) (input : Var Ecc.Mul.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.Mul.mainCircuit.call config offset input).operations region) =
      variableBaseMainSelectorTrace config := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((Ecc.Mul.mainSynthesize config input).operations region) = _
  simp only [Ecc.Mul.mainSynthesize, selector_trace_norm, Ecc.Mul.lsbGate_selector,
    Ecc.Mul.offInit, Ecc.Mul.offHi, Ecc.Mul.offLo, Ecc.Mul.offComp, Ecc.Mul.offLsb,
    Ecc.Mul.loSpan, Ecc.Mul.compSpan, variableBaseMainSelectorTrace,
    List.cons_append, List.append_assoc]

end Zcash.Snark.ZeroKnowledge
