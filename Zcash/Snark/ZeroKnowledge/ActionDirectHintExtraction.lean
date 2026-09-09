import Zcash.Snark.ZeroKnowledge.HintCellExtraction

/-!
# Direct hint readings through all three original Action stages

The original base Action's witness equations determine every directly loaded
field and point in its extractor. This covers the initial loading stage, value
and address checks, and both note stages with their actual source offsets.
Scalar windows and Merkle readings have separate extraction bridges.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- Every directly loaded Action field and point retains its original hint value. -/
theorem actionDirectHintCells_of_extendsWitnesses
    (generators : Specs.Sinsemilla.Generators) (bases : Circuit.Bases)
    (hints : Circuit.Witnesses Fp) (cfg : Circuit.Config)
    (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      ((Circuit.synthesizeBase generators bases hints cfg).operations self) self) :
    let data := Circuit.extract cfg hints self ⟨env.place, env.env.toEnvironment⟩
    data.psiOld = Witgen.MOver.eval (value := field) env hints.psiOld ∧
    data.rhoOld = Witgen.MOver.eval (value := field) env hints.rhoOld ∧
    data.nk = Witgen.MOver.eval (value := field) env hints.nk ∧
    data.vOld = Witgen.MOver.eval (value := field) env hints.vOld ∧
    data.vNew = Witgen.MOver.eval (value := field) env hints.vNew ∧
    data.psiNew = Witgen.MOver.eval (value := field) env hints.psiNew ∧
    data.magnitude = Witgen.MOver.eval (value := field) env hints.magnitude ∧
    data.sign = Witgen.MOver.eval (value := field) env hints.sign ∧
    data.cmOld = eval env hints.cmOld ∧
    data.gdOld = eval env hints.gdOld ∧
    data.akP = eval env hints.akP ∧
    data.pkdOld = eval env hints.pkDOld ∧
    data.gdNew = eval env hints.gdNew ∧
    data.pkdNew = eval env hints.pkdNew := by
  simp only [Circuit.synthesizeBase, circuit_norm] at hw
  obtain ⟨hwInitial, hwChecks, hwNotes⟩ := hw
  obtain ⟨hpsi, hrho, hnk, hvo, hvn, hcm, hgd, hak⟩ :=
    actionInitialHintCells_of_extendsWitnesses generators hints cfg self env hwInitial
  simp only [Circuit.synthWitness_output, Circuit.synthWitness_nextRegionIndex,
    Circuit.synthWitness_regionCount, Nat.add_assoc] at hwChecks hwNotes
  simp only [Circuit.synthChecks_eq, Circuit.synthChecksProgram, Circuit.loadPrivate,
    circuit_norm] at hwChecks
  obtain ⟨_, _, hmag, hsign, _, _, _, _, hwAddress⟩ := hwChecks
  simp only [Nat.add_assoc, Nat.reduceAdd] at hmag hsign hwAddress
  rw [FormalCircuit.call_operations] at hwAddress
  simp only [AddressIntegrity.circuit, circuit_norm] at hwAddress
  obtain ⟨_, hwPkd⟩ := hwAddress
  simp only [Nat.add_assoc, Nat.reduceAdd] at hwPkd
  have hpkd := witnessNonIdPoint_cells_of_extendsWitnesses cfg.eccConfig.witnessPoint
    hints.pkDOld (self + 301) env hwPkd
  simp only [Circuit.synthChecks_nextRegionIndex, Circuit.synthChecks_regionCount,
    Circuit.synthNotes_eq, Circuit.synthNotesProgram, Circuit.loadPrivate,
    circuit_norm] at hwNotes
  obtain ⟨_, hwGdNew, hwPkdNew, hpsiNew, _, _⟩ := hwNotes
  simp only [Nat.add_assoc, Nat.reduceAdd] at hwGdNew hwPkdNew hpsiNew
  have hgdNew := witnessNonIdPoint_cells_of_extendsWitnesses cfg.eccConfig.witnessPoint
    hints.gdNew (self + 347) env hwGdNew
  have hpkdNew := witnessNonIdPoint_cells_of_extendsWitnesses cfg.eccConfig.witnessPoint
    hints.pkdNew (self + 348) env hwPkdNew
  refine ⟨hpsi, hrho, hnk, hvo, hvn, ?_, ?_, ?_, hcm, hgd, hak, hpkd, hgdNew, hpkdNew⟩
  all_goals simp only [Circuit.extract, circuit_norm]
  · with_unfolding_all exact hpsiNew
  · with_unfolding_all exact hmag
  · with_unfolding_all exact hsign

end Zcash.Snark.ZeroKnowledge
