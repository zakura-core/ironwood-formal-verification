import Zcash.Snark.ZeroKnowledge.ScalarWitnessRouting

/-!
# The five scalar-window readings in the original Action

The original source routes rcv, alpha, rivk, rcmOld, and rcmNew to full-width
multiplication at regions 268, 280, 290, 328, and 375. The extracted vectors equal
the actual window programs in the same environment whenever the original witness
equations hold. No successful emission or gate-validity premise is used.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false
attribute [local irreducible] Ecc.MulFixed.FullWidth.circuit Ecc.MulFixed.Short.circuit
  ValueCommit.circuit SpendAuthority.circuit Sinsemilla.CommitDomain.commit
  CommitIvk.Main.circuit NoteCommit.Main.circuit

/-- The five original Action extractors read their actual scalar-window programs. -/
theorem actionScalarWindowReadings_of_extendsWitnesses
    (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (hints : Circuit.Witnesses Fp) (cfg : Circuit.Config)
    (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      ((Circuit.synthesizeBase generators bases hints cfg).operations self) self) :
    let data := Circuit.extract cfg hints self ⟨env.place, env.env.toEnvironment⟩
    data.rcv.1 = actionScalarWindowValues hints.rcv env ∧
    data.alpha.1 = actionScalarWindowValues hints.alpha env ∧
    data.rivk.1 = actionScalarWindowValues hints.rivk env ∧
    data.rcmOld.1 = actionScalarWindowValues hints.rcmOld env ∧
    data.rcmNew.1 = actionScalarWindowValues hints.rcmNew env := by
  simp only [Circuit.synthesizeBase, circuit_norm] at hw
  obtain ⟨_, hwChecks, hwNotes⟩ := hw
  simp only [Circuit.synthWitness_output, Circuit.synthWitness_nextRegionIndex,
    Circuit.synthWitness_regionCount, Nat.add_assoc] at hwChecks hwNotes
  simp only [Circuit.synthChecks_eq, Circuit.synthChecksProgram, Circuit.loadPrivate,
    circuit_norm] at hwChecks
  obtain ⟨_, _, _, _, hwValue, _, hwSpend, hwIvk, _⟩ := hwChecks
  simp only [Nat.add_assoc, Nat.reduceAdd] at hwValue hwSpend hwIvk
  have hrcv := valueCommit_fullWidth_witnesses bases.valueCommitV bases.valueCommitR
    (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
    _ (self+266) env hwValue
  have halpha := spendAuthority_fullWidth_witnesses bases.spendAuthG
    (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add) _ (self+280) env hwSpend
  have hrivk := commitIvk_fullWidth_witnesses generators bases.commitIvkR
    bases.ivkQ bases.ivkQ_onCurve _ _ (self+283) env hwIvk
  simp only [Circuit.synthChecks_nextRegionIndex, Circuit.synthChecks_regionCount,
    Circuit.synthNotes_eq, Circuit.synthNotesProgram, Circuit.loadPrivate,
    circuit_norm] at hwNotes
  obtain ⟨hwOld, _, _, _, hwNew, _⟩ := hwNotes
  simp only [Nat.add_assoc, Nat.reduceAdd] at hwOld hwNew
  have hrcmOld := noteCommit_fullWidth_witnesses generators bases.noteCommitR
    bases.noteQ bases.noteQ_onCurve _ _ (self+303) env hwOld
  have hrcmNew := noteCommit_fullWidth_witnesses generators bases.noteCommitR
    bases.noteQ bases.noteQ_onCurve _ _ (self+350) env hwNew
  simp only [Nat.add_assoc, Nat.reduceAdd] at hrcv hrivk hrcmOld hrcmNew
  exact ⟨fullWidth_extract_windows_of_extendsWitnesses bases.valueCommitR _ _ _ env hrcv,
    fullWidth_extract_windows_of_extendsWitnesses bases.spendAuthG _ _ _ env halpha,
    fullWidth_extract_windows_of_extendsWitnesses bases.commitIvkR _ _ _ env hrivk,
    fullWidth_extract_windows_of_extendsWitnesses bases.noteCommitR _ _ _ env hrcmOld,
    fullWidth_extract_windows_of_extendsWitnesses bases.noteCommitR _ _ _ env hrcmNew⟩

end Zcash.Snark.ZeroKnowledge
