import Zcash.Snark.ZeroKnowledge.ActionWitnessSelectorTrace

/-!
# Selector traces shared by fixed-base multiplication

The trace separates scalar decomposition, fixed-column loading, and the addition
chain. Field-valued fixed parameters and window witnesses are discarded only by
the proved operation projection; selector activations are retained in full.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

@[selector_trace_norm]
theorem incompleteAdd_regionSelectorTrace (config : Ecc.AddIncomplete.Config) (offset : ℕ)
    (input : Var Ecc.AddIncomplete.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.AddIncomplete.add.call config offset input).operations region) =
      [(config.qAddIncomplete.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem decomposeEnable_regionSelectorTrace (width : ℕ) (config : DecomposeRunningSum.Config)
    (offset count : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((DecomposeRunningSum.enableLoop width config offset count).operations region) =
      selectorRowRun config.qRangeCheck.index offset count := by
  simp only [DecomposeRunningSum.enableLoop, selector_trace_norm,
    DecomposeRunningSum.rangeCheckGate_selector, selectorRowRun, Nat.mul_one]

@[selector_trace_norm]
theorem decomposeAssign_regionSelectorTrace (width : ℕ) (config : DecomposeRunningSum.Config)
    (input : AssignedCell Fp) (offset count : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((DecomposeRunningSum.assignLoop width config input offset count).operations region) = [] := by
  simp only [DecomposeRunningSum.assignLoop, selector_trace_norm, List.ofFn_const,
    List.flatten_replicate_nil]

@[selector_trace_norm]
theorem copyDecompose_regionSelectorTrace (width count : ℕ) (config : DecomposeRunningSum.Config)
    (offset : ℕ) (input : Var DecomposeRunningSum.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((DecomposeRunningSum.copyDecompose width count).call config offset input).operations region) =
      selectorRowRun config.qRangeCheck.index offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((DecomposeRunningSum.body width count config offset input).operations region) = _
  simp only [DecomposeRunningSum.body, selector_trace_norm]

@[selector_trace_norm]
theorem fixedConstantsWindow_regionSelectorTrace (toggle : Gate Fp) (base : Ecc.MulFixed.FixedBaseData)
    (config : Ecc.MulFixed.Config) (index row : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.fixedConstantsWindow toggle base config index row).operations region) =
      [(toggle.selector.index, row)] := rfl

@[selector_trace_norm]
theorem fixedConstantsLoop_regionSelectorTrace (toggle : Gate Fp) (base : Ecc.MulFixed.FixedBaseData)
    (config : Ecc.MulFixed.Config) (offset count : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.fixedConstantsLoop toggle base config offset count).operations region) =
      selectorRowRun toggle.selector.index offset count := by
  simp only [Ecc.MulFixed.fixedConstantsLoop, selector_trace_norm, selectorRowRun, Nat.mul_one]

@[selector_trace_norm]
theorem fixedWindow_regionSelectorTrace (base : Ecc.MulFixed.FixedBaseData)
    (table : ℕ → ℕ → Point Fp) (config : Ecc.MulFixed.Config) (input : AssignedCell Fp)
    (index row : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.processWindow base table config input index row).operations region) = [] := rfl

/-- The first incomplete addition precedes the remaining middle-window additions. -/
def fixedWindowChainSelectorTrace (config : Ecc.MulFixed.Config) (offset count : ℕ) : List (ℕ × ℕ) :=
  [(config.addIncompleteConfig.qAddIncomplete.index, offset + 1)] ++
    selectorRowRun config.addIncompleteConfig.qAddIncomplete.index (offset + 2) (count - 3)

/-- Any selector-free window witness routine gives the same shared addition trace. -/
theorem fixedWindowChain_regionSelectorTrace (config : Ecc.MulFixed.Config)
    (process : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp))) (offset count : ℕ) (region : RegionIndex)
    (hprocess : ∀ index row, regionSelectorTrace ((process index row).operations region) = []) :
    regionSelectorTrace ((Ecc.MulFixed.windowChain config process offset count).operations region) =
      fixedWindowChainSelectorTrace config offset count := by
  simp only [Ecc.MulFixed.windowChain, Ecc.MulFixed.windowChainStep, selector_trace_norm,
    hprocess, fixedWindowChainSelectorTrace, selectorRowRun, Nat.mul_one]

@[selector_trace_norm]
theorem fullWidthWindow_regionSelectorTrace (base : Ecc.MulFixed.FixedBaseData)
    (config : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (index row : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.FullWidth.processWindowH base config windows index row).operations region) = [] := rfl

@[selector_trace_norm]
theorem fullWidthScalar_regionSelectorTrace (config : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.FullWidth.witnessScalarLoop config windows offset).operations region) =
      selectorRowRun config.qMulFixedFull.index offset 85 := by
  simp only [Ecc.MulFixed.FullWidth.witnessScalarLoop, selector_trace_norm,
    Ecc.MulFixed.FullWidth.fullWidthGate_selector, selectorRowRun, Nat.mul_one,
    List.ofFn_const, List.flatten_replicate_nil]

/-- The scalar and fixed-constant passes each enable the full-width selector. -/
def fullWidthInnerSelectorTrace (config : Ecc.MulFixed.FullWidth.Config) (offset : ℕ) : List (ℕ × ℕ) :=
  selectorRowRun config.qMulFixedFull.index offset 85 ++
    selectorRowRun config.qMulFixedFull.index offset 85 ++
    fixedWindowChainSelectorTrace config.superConfig offset 85

@[selector_trace_norm]
theorem fullWidthInner_regionSelectorTrace (base : Ecc.MulFixed.FixedBaseData)
    (config : Ecc.MulFixed.FullWidth.Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (region : RegionIndex) :
    regionSelectorTrace ((Ecc.MulFixed.FullWidth.innerRegion base config offset windows).operations region) =
      fullWidthInnerSelectorTrace config offset := by
  rw [Ecc.MulFixed.FullWidth.innerRegion_operations_eq]
  simp only [selector_trace_norm, Ecc.MulFixed.FullWidth.fullWidthGate_selector]
  rw [fixedWindowChain_regionSelectorTrace _ _ _ _ _ (fun index row =>
    fullWidthWindow_regionSelectorTrace base config windows index row region)]
  rfl

/-- Both regions of full-width multiplication, in their synthesis order. -/
@[selector_trace_norm]
theorem fullWidth_selectorTrace (base : Ecc.MulFixed.FixedBase) (config : Ecc.MulFixed.FullWidth.Config)
    (input : Var UnconstrainedNat Fp) (region : RegionIndex) :
    selectorTrace (((Ecc.MulFixed.FullWidth.circuit base).call config input).operations region) =
      [fullWidthInnerSelectorTrace config 0, [(config.superConfig.addConfig.qAdd.index, 0)]] := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((Ecc.MulFixed.FullWidth.synthesize base.toData config
    (Ecc.MulFixed.FullWidth.scalarWindows input)).operations region) = _
  simp only [Ecc.MulFixed.FullWidth.synthesize, selector_trace_norm, List.cons_append]

end Zcash.Snark.ZeroKnowledge
