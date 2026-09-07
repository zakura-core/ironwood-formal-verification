import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Circuits.Utilities.LookupRangeCheck

/-!
# Exact selector traces of the range-check gadgets

Both running-sum selectors are retained at every running row. Short checks enable
the lookup selector twice and the bitshift gate at the second row. These source
equations do not depend on witness values or on the strict-tail constraint.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The two selector activations at each row of a running-sum check. -/
def runningSelectorTrace {K : ℕ} (config : LookupRangeCheck.Config K) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count =>
    [(config.qLookup.index, offset + i.val), (config.qRunning.index, offset + i.val)]).flatten

@[selector_trace_norm]
theorem rangeCheckRound_regionSelectorTrace (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (index row : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((LookupRangeCheck.rangeCheckRound K config element index row).operations region) =
      [(config.qLookup.index, row), (config.qRunning.index, row)] := rfl

@[selector_trace_norm]
theorem rangeCheckLoop_regionSelectorTrace (K : ℕ) (config : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (offset count : ℕ) (region : RegionIndex) :
    regionSelectorTrace ((LookupRangeCheck.rangeCheckLoop K config element offset count).operations region) =
      runningSelectorTrace config offset count := by
  simp only [LookupRangeCheck.rangeCheckLoop, selector_trace_norm, Nat.mul_one,
    runningSelectorTrace]

@[selector_trace_norm]
theorem shortRangeCheck_regionSelectorTrace (K bits : ℕ) (config : LookupRangeCheck.Config K)
    (offset : ℕ) (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((LookupRangeCheck.shortRangeCheck K bits).call config offset input).operations region) =
      [(config.qLookup.index, offset), (config.qLookup.index, offset + 1),
        (config.qBitshift.index, offset + 1)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem rangeCheck_regionSelectorTrace (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((LookupRangeCheck.rangeCheck K count strict).call config offset input).operations region) =
      runningSelectorTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((LookupRangeCheck.rangeCheckBody K count strict config offset input).operations region) = _
  cases strict <;>
    simp only [LookupRangeCheck.rangeCheckBody, selector_trace_norm, Bool.false_eq_true,
      if_false, if_true]

@[selector_trace_norm]
theorem rangeCheckAt_regionSelectorTrace (K count : ℕ) (strict : Bool)
    (hstrict : strict = true → 0 < count) (config : LookupRangeCheck.Config K) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((LookupRangeCheck.rangeCheckAt K count strict hstrict).call config offset input).operations region) =
      runningSelectorTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((LookupRangeCheck.rangeCheckAtBody K count strict config offset input).operations region) = _
  cases strict <;>
    simp only [LookupRangeCheck.rangeCheckAtBody, selector_trace_norm, Bool.false_eq_true,
      if_false, if_true]

@[selector_trace_norm]
theorem rangeCheckAtDecomposed_regionSelectorTrace (count : ℕ) (hcount : 13 ≤ count)
    (hpow : 10 * count ≤ 254) (config : LookupRangeCheck.Config 10) (offset : ℕ)
    (input : Var unit Fp) (region : RegionIndex) :
    regionSelectorTrace (((LookupRangeCheck.rangeCheckAtDecomposed count hcount hpow).call config offset input).operations region) =
      runningSelectorTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((LookupRangeCheck.rangeCheckAtDecomposedBody count config offset input).operations region) = _
  simp only [LookupRangeCheck.rangeCheckAtDecomposedBody, selector_trace_norm]

@[selector_trace_norm]
theorem copyCheck_selectorTrace (K count : ℕ) (strict : Bool)
    (config : LookupRangeCheck.Config K) (input : Var LookupRangeCheck.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((LookupRangeCheck.copyCheck K count strict).call config input).operations region) =
      [runningSelectorTrace config 0 count] := by
  simp only [LookupRangeCheck.copyCheck, selector_trace_norm]

end Zcash.Snark.ZeroKnowledge
