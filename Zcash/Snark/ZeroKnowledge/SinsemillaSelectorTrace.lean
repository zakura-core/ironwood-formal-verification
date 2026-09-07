import Zcash.Snark.ZeroKnowledge.SelectorTracePrograms
import Zcash.Circuits.Sinsemilla.HashToPoint

/-!
# Exact selector traces of Sinsemilla hashing

Lookup and gate activations are both retained, including repeated activation of
the same selector at a row. The formulas preserve piece order and boundary rows
without evaluating generator points, message pieces, or witness programs.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- Each interior Sinsemilla row enables the lookup and then the gate. -/
def sinsemillaRoundsSelectorTrace (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin count =>
    [(config.qS1.index, offset + i.val), (config.qS1.index, offset + i.val)]).flatten

/-- A piece ends with the boundary lookup; its linking gate belongs to the chain. -/
def sinsemillaPieceSelectorTrace (config : Sinsemilla.HashPiece.Config) (offset count : ℕ) :
    List (ℕ × ℕ) :=
  sinsemillaRoundsSelectorTrace config offset count ++ [(config.qS1.index, offset + count)]

@[selector_trace_norm]
theorem sinsemillaRound_regionSelectorTrace (generators : Specs.Sinsemilla.Generators) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.HashPiece.round generators index).call config offset input).operations region) =
      [(config.qS1.index, offset), (config.qS1.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem sinsemillaLoop_regionSelectorTrace (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.HashPiece.loop generators count).call config offset input).operations region) =
      sinsemillaRoundsSelectorTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.loop, selector_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellVec,
    sinsemillaRoundsSelectorTrace, Nat.mul_one]

@[selector_trace_norm]
theorem sinsemillaPiece_regionSelectorTrace (generators : Specs.Sinsemilla.Generators) (count : ℕ)
    (final : Bool) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.HashPiece.circuit generators count final initialY).call
      config offset input).operations region) = sinsemillaPieceSelectorTrace config offset count := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((Sinsemilla.HashPiece.circuitBody generators count final initialY
    config offset input).operations region) = _
  simp only [Sinsemilla.HashPiece.circuitBody, selector_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt,
    Sinsemilla.HashPiece.operations_cellVec, sinsemillaPieceSelectorTrace]
  rfl

@[selector_trace_norm]
theorem sinsemillaSlot_regionSelectorTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp) (index : ℕ)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (input : AssignedCell Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.Chain.slot generators widths initialY index).call
      config offset input).operations region) = sinsemillaPieceSelectorTrace config offset (widths.getD index 0) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.slot, selector_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt]

/-- Every piece and its boundary linking gate, in the chain's exact loop order. -/
def sinsemillaChainSelectorTrace (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (ℕ × ℕ) :=
  (List.ofFn fun i : Fin widths.length =>
    let base := offset + Sinsemilla.Chain.prefixRows widths i.val
    sinsemillaPieceSelectorTrace config base (widths.getD i.val 0) ++
      [(config.qS1.index, base + widths.getD i.val 0)]).flatten

@[selector_trace_norm]
theorem sinsemillaChain_regionSelectorTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (initialY : Placed Environment Fp → Fp)
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.Chain.circuit generators widths initialY).call
      config offset input).operations region) = sinsemillaChainSelectorTrace config offset widths := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.circuit, selector_trace_norm,
    Sinsemilla.HashPiece.operations_readState, Sinsemilla.HashPiece.operations_cellAt,
    Sinsemilla.HashPiece.sinsemillaGate_selector, sinsemillaChainSelectorTrace]
  rfl

/-- The domain-point initialization gate followed by all message-piece activations. -/
def sinsemillaHashSelectorTrace (config : Sinsemilla.HashPiece.Config) (offset : ℕ) (widths : List ℕ) :
    List (ℕ × ℕ) :=
  [(config.qS4.index, offset)] ++ sinsemillaChainSelectorTrace config offset widths

@[selector_trace_norm]
theorem sinsemillaHash_regionSelectorTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.HashToPoint.hashRegion generators widths point honCurve hwidths).call
      config offset input).operations region) = sinsemillaHashSelectorTrace config offset widths := by
  rw [FormalRegionCircuit.call_operations]
  change regionSelectorTrace ((Sinsemilla.HashToPoint.hashRegionSynthesize generators widths point
    config offset input).operations region) = _
  simp only [Sinsemilla.HashToPoint.hashRegionSynthesize, selector_trace_norm,
    Sinsemilla.HashToPoint.z1Cells_operations, sinsemillaHashSelectorTrace]
  rfl

@[selector_trace_norm]
theorem sinsemillaHash_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (widths : List ℕ) (point : Point Fp) (honCurve : point.OnCurve) (hwidths : widths ≠ [])
    (config : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs widths.length) Fp) (region : RegionIndex) :
    selectorTrace (((Sinsemilla.HashToPoint.hashCircuit generators widths point honCurve hwidths).call
      config input).operations region) = [sinsemillaHashSelectorTrace config 0 widths] := by
  simp only [Sinsemilla.HashToPoint.hashCircuit, selector_trace_norm]

@[selector_trace_norm]
theorem witnessMessagePiece_selectorTrace (config : Sinsemilla.HashPiece.Config) (witness : WitgenIR Fp 1)
    (region : RegionIndex) :
    selectorTrace ((Sinsemilla.HashToPoint.witnessMessagePiece config witness).operations region) = [[]] := rfl

end Zcash.Snark.ZeroKnowledge
