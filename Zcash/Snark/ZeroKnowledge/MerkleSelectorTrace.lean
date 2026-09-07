import Zcash.Snark.ZeroKnowledge.SinsemillaSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace
import Zcash.Snark.ZeroKnowledge.SelectorTraceFold
import Zcash.Circuits.Sinsemilla.Merkle

/-!
# Exact selector traces of the Merkle-path circuit

The per-layer trace has eight regions: the conditional swap followed by seven
hash-layer regions. A serial path is proved to concatenate this trace at each
layer, independently of the node, sibling, and direction witnesses.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

@[selector_trace_norm]
theorem condSwap_regionSelectorTrace (sibling : WitgenIR Fp 1)
    (swap : Placed ProverEnvironment Fp → Bool) (config : CondSwap.Config)
    (offset : ℕ) (input : Var CondSwap.Input Fp) (region : RegionIndex) :
    regionSelectorTrace (((CondSwap.swap sibling swap).call config offset input).operations region) =
      [(config.qSwap.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

@[selector_trace_norm]
theorem merkleDecomposition_regionSelectorTrace (level : Fp) (config : Sinsemilla.Merkle.Gate.Config)
    (offset : ℕ) (input : Var Sinsemilla.Merkle.Gate.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((Sinsemilla.Merkle.Gate.circuit level).call config offset input).operations region) =
      [(config.qDecompose.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- The seven source regions of a Merkle hash layer, including three selector-free loads. -/
def merkleHashSelectorTrace (config : Sinsemilla.Merkle.Config) (lookup : LookupRangeCheck.Config 10) :
    List (List (ℕ × ℕ)) :=
  [[], [(lookup.qLookup.index, 0), (lookup.qLookup.index, 1), (lookup.qBitshift.index, 1)],
    [(lookup.qLookup.index, 0), (lookup.qLookup.index, 1), (lookup.qBitshift.index, 1)],
    [], [], sinsemillaHashSelectorTrace config.sinsemilla 0 Sinsemilla.Merkle.HashLayer.merkleNs,
    [(config.gate.qDecompose.index, 0)]]

@[selector_trace_norm]
theorem merkleHash_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level : ℕ) (hlevel : level < 2 ^ 10)
    (config : Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.HashLayer.Input Fp) (region : RegionIndex) :
    selectorTrace (((Sinsemilla.Merkle.HashLayer.circuit generators point honCurve level hlevel).call
      config input).operations region) = merkleHashSelectorTrace config.1 config.2 := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((Sinsemilla.Merkle.HashLayer.synthesize generators config.1 config.2
    point honCurve level input).operations region) = _
  simp only [Sinsemilla.Merkle.HashLayer.synthesize, Sinsemilla.HashToPoint.hashMessage,
    selector_trace_norm, merkleHashSelectorTrace, List.cons_append]

/-- A layer's conditional-swap region precedes its hash-layer regions. -/
def merkleLayerSelectorTrace
    (config : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10) :
    List (List (ℕ × ℕ)) :=
  [(config.1.qSwap.index, 0)] :: merkleHashSelectorTrace config.2.1 config.2.2

@[selector_trace_norm]
theorem merkleLayer_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level : ℕ) (hlevel : level < 2 ^ 10)
    (sibling : WitgenIR Fp 1) (swap : Placed ProverEnvironment Fp → Bool)
    (config : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp) (region : RegionIndex) :
    selectorTrace (((Sinsemilla.Merkle.Layer.circuit generators point honCurve level hlevel sibling swap).call
      config input).operations region) = merkleLayerSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.Merkle.Layer.circuit, selector_trace_norm,
    merkleLayerSelectorTrace, List.cons_append]

/-- Every source region in a serial Merkle path, with no witness-dependent trace data. -/
@[selector_trace_norm]
theorem merkleRoot_selectorTrace (generators : Specs.Sinsemilla.Generators)
    (point : Point Fp) (honCurve : point.OnCurve) (level depth : ℕ) (hdepth : level + depth ≤ 2 ^ 10)
    (siblings : ℕ → WitgenIR Fp 1) (swaps : ℕ → Placed ProverEnvironment Fp → Bool)
    (config : CondSwap.Config × Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp) (region : RegionIndex) :
    selectorTrace (((Sinsemilla.Merkle.CalculateRoot.circuit generators point honCurve level depth hdepth
      siblings swaps).call config input).operations region) =
      (List.replicate depth (merkleLayerSelectorTrace config)).flatten := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((do
    let output ← FormalCircuit.foldCall
      (Sinsemilla.Merkle.CalculateRoot.layerAt generators point honCurve level siblings swaps)
      Sinsemilla.Merkle.CalculateRoot.toInput config input depth
    pure output.node : Circuit Fp (AssignedCell Fp)).operations region) = _
  simp only [selector_trace_norm]
  trans (List.ofFn fun _ : Fin depth => merkleLayerSelectorTrace config).flatten
  · apply selectorTrace_foldCall (traces := fun _ => merkleLayerSelectorTrace config)
    intro index input current
    simp only [Sinsemilla.Merkle.CalculateRoot.layerAt, selector_trace_norm]
  · simp

end Zcash.Snark.ZeroKnowledge
