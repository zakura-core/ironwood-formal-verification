import Zcash.Snark.ZeroKnowledge.CommitDomainSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace

/-!
# Selector trace of the incoming viewing-key commitment

All fourteen regions are derived from the source stages: seven message-piece
regions, the four-region Sinsemilla commitment, and three canonicity regions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The incoming-viewing-key check enables its selector at the requested row, supplying the source
metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem commitIvkGate_regionSelectorTrace (first second : WitgenIR Fp 1) (config : CommitIvk.Config)
    (offset : ℕ) (input : Var CommitIvk.Inputs Fp) (region : RegionIndex) :
    regionSelectorTrace (((CommitIvk.bundle first second).call config offset input).operations region) =
      [(config.qCommitIvk.index, offset)] := by
  rw [FormalRegionCircuit.call_operations]
  rfl

/-- Incoming-viewing-key canonicity retains both range-check traces and its final gate, supplying
the source metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem commitIvkCanonicity_selectorTrace (first second : WitgenIR Fp 1)
    (config : CommitIvk.Config × LookupRangeCheck.Config 10)
    (input : Var CommitIvk.Canonicity.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((CommitIvk.Canonicity.circuit first second).call config input).operations region) =
      [runningSelectorTrace config.2 0 13, runningSelectorTrace config.2 0 14,
        [(config.1.qCommitIvk.index, 0)]] := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((CommitIvk.Canonicity.synth first second config.1 config.2 input).operations region) = _
  simp only [CommitIvk.Canonicity.synth, CommitIvk.Canonicity.gateChild,
    selector_trace_norm, List.cons_append]

/-- The seven interleaved message loads and short checks. -/
def commitIvkPiecesSelectorTrace (config : CommitIvk.Main.Config) : List (List (ℕ × ℕ)) :=
  let short := shortSelectorTrace config.lookupConfig
  [[], short, short, [], [], short, []]

/-- Incoming-viewing-key message preparation retains its complete configured trace, supplying the
source metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem commitIvkPieces_selectorTrace (config : CommitIvk.Main.Config)
    (ak nk : AssignedCell Fp) (region : RegionIndex) :
    selectorTrace ((CommitIvk.Main.synthPieces config ak nk).operations region) =
      commitIvkPiecesSelectorTrace config := by
  simp only [CommitIvk.Main.synthPieces, selector_trace_norm,
    commitIvkPiecesSelectorTrace, shortSelectorTrace, List.cons_append]

/-- All source regions of the incoming viewing-key commitment. -/
def commitIvkSelectorTrace (config : CommitIvk.Main.Config) : List (List (ℕ × ℕ)) :=
  commitIvkPiecesSelectorTrace config ++
    sinsemillaCommitSelectorTrace CommitIvk.Main.ns (config.mulConfig, config.hashConfig, config.addConfig) ++
    [runningSelectorTrace config.lookupConfig 0 13, runningSelectorTrace config.lookupConfig 0 14,
      [(config.gate.qCommitIvk.index, 0)]]

/-- The complete incoming-viewing-key commitment produces its configured source trace, supplying the
source metadata for Action selector coverage. -/
@[selector_trace_norm]
theorem commitIvk_selectorTrace (generators : Specs.Sinsemilla.Generators) (base : Ecc.MulFixed.FixedBase)
    (point : Point Fp) (honCurve : point.OnCurve) (config : CommitIvk.Main.Config)
    (input : Var CommitIvk.Main.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((CommitIvk.Main.circuit generators base point honCurve).call config input).operations region) =
      commitIvkSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((CommitIvk.Main.synth generators base point honCurve config input).operations region) = _
  simp only [CommitIvk.Main.synth, selector_trace_norm, NoteCommit.Main.currentRegion_operations,
    commitIvkSelectorTrace, List.append_assoc]

end Zcash.Snark.ZeroKnowledge
