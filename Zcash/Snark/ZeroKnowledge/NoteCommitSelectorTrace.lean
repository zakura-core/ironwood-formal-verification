import Zcash.Snark.ZeroKnowledge.NoteGateSelectorTrace
import Zcash.Snark.ZeroKnowledge.CommitDomainSelectorTrace
import Zcash.Snark.ZeroKnowledge.LookupSelectorTrace
import Zcash.Circuits.NoteCommit.MainBundle

/-!
# Complete source selector trace of note commitment

All forty-three regions are retained in source order: fifteen piece-loading
regions, eighteen hash and canonicity-check regions, and ten final gate regions.
The trace is independent of note data and commitment blinding witnesses.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The five-region y-coordinate canonicity flow. -/
def noteYSelectorTrace (config : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10) :
    List (List (ℕ × ℕ)) :=
  [shortSelectorTrace config.2, shortSelectorTrace config.2,
    runningSelectorTrace config.2 0 25, runningSelectorTrace config.2 0 13,
    [(config.1.qYCanon.index, 0)]]

@[selector_trace_norm]
theorem noteY_selectorTrace (witness : WitgenIR Fp 1)
    (config : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10)
    (input : Var NoteCommit.YCanonicityCheck.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((NoteCommit.YCanonicityCheck.circuit witness).call config input).operations region) =
      noteYSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((NoteCommit.YCanonicityCheck.synth witness config.1 config.2 input).operations region) = _
  simp only [NoteCommit.YCanonicityCheck.synth, NoteCommit.YCanonicityCheck.gateChild,
    selector_trace_norm, noteYSelectorTrace, shortSelectorTrace, List.cons_append]

/-- The fifteen interleaved message-piece loads and short checks. -/
def notePiecesSelectorTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  let short := shortSelectorTrace config.lookupConfig
  [[], short, short, [], [], short, [], short, short, [], [], short, [], short, []]

@[selector_trace_norm]
theorem notePieces_selectorTrace (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (region : RegionIndex) :
    selectorTrace ((NoteCommit.Main.synthPieces config input).operations region) =
      notePiecesSelectorTrace config := by
  simp only [NoteCommit.Main.synthPieces, selector_trace_norm,
    notePiecesSelectorTrace, shortSelectorTrace, List.cons_append]

/-- The eighteen regions between piece loading and the final gate stages. -/
def noteChecksSelectorTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  noteYSelectorTrace (config.gates.y, config.lookupConfig) ++
    noteYSelectorTrace (config.gates.y, config.lookupConfig) ++
    sinsemillaCommitSelectorTrace NoteCommit.Main.ns (config.mulConfig, config.hashConfig, config.addConfig) ++
    [runningSelectorTrace config.lookupConfig 0 13, runningSelectorTrace config.lookupConfig 0 14,
      runningSelectorTrace config.lookupConfig 0 14, runningSelectorTrace config.lookupConfig 0 13]

@[selector_trace_norm]
theorem noteChecks_selectorTrace (generators : Specs.Sinsemilla.Generators) (base : Ecc.MulFixed.FixedBase)
    (point : Point Fp) (honCurve : point.OnCurve) (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (pieces : NoteCommit.Main.PieceCells)
    (hashRegion region : RegionIndex) :
    selectorTrace ((NoteCommit.Main.synthChecks generators base point honCurve config input pieces hashRegion).operations region) =
      noteChecksSelectorTrace config := by
  simp only [NoteCommit.Main.synthChecks, selector_trace_norm,
    noteChecksSelectorTrace, List.cons_append, List.append_assoc]

/-- Five decomposition gates followed by five canonicity gates. -/
def noteGatesSelectorTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  [[(config.gates.b.qNotecommitB.index, 0)], [(config.gates.d.qNotecommitD.index, 0)],
    [(config.gates.e.qNotecommitE.index, 0)], [(config.gates.g.qNotecommitG.index, 0)],
    [(config.gates.h.qNotecommitH.index, 0)], [(config.gates.gd.qNotecommitGd.index, 0)],
    [(config.gates.pkd.qNotecommitPkd.index, 0)], [(config.gates.value.qNotecommitValue.index, 0)],
    [(config.gates.rho.qNotecommitRho.index, 0)], [(config.gates.psi.qNotecommitPsi.index, 0)]]

@[selector_trace_norm]
theorem noteGates_selectorTrace (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (pieces : NoteCommit.Main.PieceCells)
    (checks : NoteCommit.Main.CheckCells) (hashRegion region : RegionIndex) :
    selectorTrace ((NoteCommit.Main.synthGates config input pieces checks hashRegion).operations region) =
      noteGatesSelectorTrace config := by
  simp only [NoteCommit.Main.synthGates, NoteCommit.Main.synthDecompositions,
    NoteCommit.Main.synthCanonicity, NoteCommit.Main.synthGdPkdValueCanonicity,
    NoteCommit.Main.synthRhoPsiCanonicity, selector_trace_norm,
    noteGatesSelectorTrace, List.cons_append]

/-- The complete note-commitment source trace, before global region placement. -/
def noteCommitSelectorTrace (config : NoteCommit.Main.Config) : List (List (ℕ × ℕ)) :=
  notePiecesSelectorTrace config ++ noteChecksSelectorTrace config ++ noteGatesSelectorTrace config

@[selector_trace_norm]
theorem noteCommit_selectorTrace (generators : Specs.Sinsemilla.Generators) (base : Ecc.MulFixed.FixedBase)
    (point : Point Fp) (honCurve : point.OnCurve) (config : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (region : RegionIndex) :
    selectorTrace (((NoteCommit.Main.circuit generators base point honCurve).call config input).operations region) =
      noteCommitSelectorTrace config := by
  rw [FormalCircuit.call_operations]
  change selectorTrace ((NoteCommit.Main.synth generators base point honCurve config input).operations region) = _
  simp only [NoteCommit.Main.synth, selector_trace_norm, NoteCommit.Main.currentRegion_operations,
    noteCommitSelectorTrace, List.append_assoc]

end Zcash.Snark.ZeroKnowledge
