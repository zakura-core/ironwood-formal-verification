import Zcash.Circuits.Action.Bundle

/-!
# Exact hint readings from the original loading programs

Witness consistency fixes the scalar and point cells to their supplied programs.
The Action corollary covers every field and point in the original first stage,
for arbitrary hints, configuration, placement, and environment. These lemmas
connect existing witness equations to the extractor; they do not assume gate
validity or replace the global witness-consistency proof.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The original scalar-loading region retains its exact witness-program output. -/
theorem loadPrivate_cell_of_extendsWitnesses
    (column : Column .advice) (program : WitgenIR Fp 1)
    (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      ((Action.Circuit.loadPrivate column program).operations self) self) :
    eval (⟨env.place, env.env.toEnvironment⟩ : Placed Environment Fp)
        (AssignedCell.of self 0 column : Var field Fp) =
      (program.eval env)[0] := by
  simpa only [Action.Circuit.loadPrivate, circuit_norm] using hw

/-- The original point-loading region retains both coordinates of its exact point hint. -/
theorem witnessPoint_cells_of_extendsWitnesses
    (cfg : Ecc.WitnessPoint.Config) (program : Var (Unconstrained Point) Fp)
    (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      ((Ecc.WitnessPoint.pointFormal.call cfg program).operations self) self) :
    (⟨eval (⟨env.place, env.env.toEnvironment⟩ : Placed Environment Fp)
        (AssignedCell.of self 0 cfg.x : Var field Fp),
      eval (⟨env.place, env.env.toEnvironment⟩ : Placed Environment Fp)
        (AssignedCell.of self 0 cfg.y : Var field Fp)⟩ : Point Fp) = eval env program := by
  rw [FormalCircuit.call_operations] at hw
  simp only [Ecc.WitnessPoint.pointFormal, Ecc.WitnessPoint.point,
    FormalRegionCircuit.toFormal, circuit_norm,
    RegionOperation.extendsWitness_assignAdvice] at hw
  apply Point.ext_coords
  simp only [Point.coords, circuit_norm, explicit_provable_type]
  exact Prod.ext hw.1 hw.2

/-- The nonidentity point loader has the same exact hint-to-cell correspondence. -/
theorem witnessNonIdPoint_cells_of_extendsWitnesses
    (cfg : Ecc.WitnessPoint.Config) (program : Var (Unconstrained Point) Fp)
    (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      ((Ecc.WitnessPoint.pointNonIdFormal.call cfg program).operations self) self) :
    (⟨eval (⟨env.place, env.env.toEnvironment⟩ : Placed Environment Fp)
        (AssignedCell.of self 0 cfg.x : Var field Fp),
      eval (⟨env.place, env.env.toEnvironment⟩ : Placed Environment Fp)
        (AssignedCell.of self 0 cfg.y : Var field Fp)⟩ : Point Fp) = eval env program := by
  rw [FormalCircuit.call_operations] at hw
  simp only [Ecc.WitnessPoint.pointNonIdFormal, Ecc.WitnessPoint.pointNonId,
    FormalRegionCircuit.toFormal, circuit_norm,
    RegionOperation.extendsWitness_assignAdvice] at hw
  apply Point.ext_coords
  simp only [Point.coords, circuit_norm, explicit_provable_type]
  exact Prod.ext hw.1 hw.2

/-- All fields and points loaded by the original first Action stage equal their hints. -/
theorem actionInitialHintCells_of_extendsWitnesses
    (generators : Specs.Sinsemilla.Generators) (hints : Action.Circuit.Witnesses Fp)
    (cfg : Action.Circuit.Config) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      ((Action.Circuit.synthWitness generators hints cfg).operations self) self) :
    let data := Action.Circuit.extract cfg hints self ⟨env.place, env.env.toEnvironment⟩
    data.psiOld = Witgen.MOver.eval (value := field) env hints.psiOld ∧
    data.rhoOld = Witgen.MOver.eval (value := field) env hints.rhoOld ∧
    data.nk = Witgen.MOver.eval (value := field) env hints.nk ∧
    data.vOld = Witgen.MOver.eval (value := field) env hints.vOld ∧
    data.vNew = Witgen.MOver.eval (value := field) env hints.vNew ∧
    data.cmOld = eval env hints.cmOld ∧
    data.gdOld = eval env hints.gdOld ∧
    data.akP = eval env hints.akP := by
  simp only [Action.Circuit.synthWitness, Action.Circuit.loadPrivate, Sinsemilla.load,
    circuit_norm] at hw
  obtain ⟨-, -, -, -, -, -, hpsi, hrho, hcm, hgd, hak, hnk, hvo, hvn⟩ := hw
  simp only [Nat.add_assoc, Nat.reduceAdd] at hgd hak hnk hvo hvn
  refine ⟨?_, ?_, ?_, ?_, ?_,
    witnessPoint_cells_of_extendsWitnesses cfg.eccConfig.witnessPoint hints.cmOld
      (self + 2) env hcm,
    witnessNonIdPoint_cells_of_extendsWitnesses cfg.eccConfig.witnessPoint hints.gdOld
      (self + 3) env hgd,
    witnessNonIdPoint_cells_of_extendsWitnesses cfg.eccConfig.witnessPoint hints.akP
      (self + 4) env hak⟩
  all_goals simp only [Action.Circuit.extract]
  all_goals simp only [circuit_norm] at hpsi hrho hnk hvo hvn ⊢
  · with_unfolding_all exact hpsi
  · with_unfolding_all exact hrho
  · with_unfolding_all exact hnk
  · with_unfolding_all exact hvo
  · with_unfolding_all exact hvn

end Zcash.Snark.ZeroKnowledge
