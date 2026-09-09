import Zcash.Snark.ZeroKnowledge.ScalarWitnessExtraction

/-!
# Routing original commitment witnesses to scalar extraction

These source equations locate the full-width scalar calls in ValueCommit,
spend authority, Sinsemilla commitments, CommitIvk, and note commitments.
Every conclusion concerns the original child call with its exact scalar program
and source region, without assuming gate validity.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Ecc.MulFixed (FixedBase)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] Ecc.MulFixed.FullWidth.circuit Ecc.MulFixed.Short.circuit
  ValueCommit.circuit SpendAuthority.circuit Sinsemilla.CommitDomain.commit
  CommitIvk.Main.circuit NoteCommit.Main.circuit

/-- The original ValueCommit source contains its blinding multiplication at offset two. -/
theorem valueCommit_fullWidth_witnesses
    (valueBase : Ecc.MulFixed.Short.FixedBase) (blindBase : FixedBase)
    (cfg : Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var ValueCommit.Inputs Fp) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      (((ValueCommit.circuit valueBase blindBase).call cfg input).operations self) self) :
    ExtendsWitnesses env.place env.env
      (((Ecc.MulFixed.FullWidth.circuit blindBase).call cfg.2.1 input.rcv).operations (self+2)) (self+2) := by
  rw [FormalCircuit.call_operations] at hw
  simp only [ValueCommit.circuit, circuit_norm] at hw
  exact hw.2.1

/-- The original spend-authority source starts with its scalar multiplication. -/
theorem spendAuthority_fullWidth_witnesses
    (base : FixedBase) (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var SpendAuthority.Input Fp) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      (((SpendAuthority.circuit base).call cfg input).operations self) self) :
    ExtendsWitnesses env.place env.env
      (((Ecc.MulFixed.FullWidth.circuit base).call cfg.1 input.alpha).operations self) self := by
  rw [FormalCircuit.call_operations] at hw
  simp only [SpendAuthority.circuit, circuit_norm] at hw
  exact hw.1

/-- The original Sinsemilla commitment starts with its scalar blinding multiplication. -/
theorem sinsemillaCommit_fullWidth_witnesses
    (generators : Specs.Sinsemilla.Generators) (sizes : List ℕ) (base : FixedBase)
    (point : Point Fp) (hon : point.OnCurve) (hsizes : sizes ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config × Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (input : Var (Sinsemilla.CommitDomain.Input sizes.length) Fp)
    (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      (((Sinsemilla.CommitDomain.commit generators sizes base point hon hsizes).call cfg input).operations self) self) :
    ExtendsWitnesses env.place env.env
      (((Ecc.MulFixed.FullWidth.circuit base).call cfg.1 input.r).operations self) self := by
  rw [FormalCircuit.call_operations] at hw
  simp only [Sinsemilla.CommitDomain.commit, Sinsemilla.CommitDomain.synthesize, circuit_norm] at hw
  exact hw.1

/-- CommitIvk's original scalar call occurs after its seven message-piece regions. -/
theorem commitIvk_fullWidth_witnesses
    (generators : Specs.Sinsemilla.Generators) (base : FixedBase)
    (point : Point Fp) (hon : point.OnCurve) (cfg : CommitIvk.Main.Config)
    (input : Var CommitIvk.Main.Inputs Fp) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      (((CommitIvk.Main.circuit generators base point hon).call cfg input).operations self) self) :
    ExtendsWitnesses env.place env.env
      (((Ecc.MulFixed.FullWidth.circuit base).call cfg.mulConfig input.rivk).operations (self+7)) (self+7) := by
  rw [FormalCircuit.call_operations] at hw
  simp only [CommitIvk.Main.circuit, CommitIvk.Main.synth, circuit_norm] at hw
  exact sinsemillaCommit_fullWidth_witnesses generators _ base point hon _ _ _ (self+7) env hw.2.1

/-- Each original note commitment reaches its scalar call after 25 source regions. -/
theorem noteCommit_fullWidth_witnesses
    (generators : Specs.Sinsemilla.Generators) (base : FixedBase)
    (point : Point Fp) (hon : point.OnCurve) (cfg : NoteCommit.Main.Config)
    (input : Var NoteCommit.Main.Inputs Fp) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      (((NoteCommit.Main.circuit generators base point hon).call cfg input).operations self) self) :
    ExtendsWitnesses env.place env.env
      (((Ecc.MulFixed.FullWidth.circuit base).call cfg.mulConfig input.rcm).operations (self+25)) (self+25) := by
  rw [FormalCircuit.call_operations] at hw
  simp only [NoteCommit.Main.circuit, NoteCommit.Main.synth, circuit_norm] at hw
  have hwChecks := hw.2.1
  simp only [NoteCommit.Main.synthChecks, circuit_norm] at hwChecks
  have hwCommit := hwChecks.2.2.1
  simp only [Nat.add_assoc, Nat.reduceAdd] at hwCommit
  exact sinsemillaCommit_fullWidth_witnesses generators _ base point hon _ _ _ (self+25) env hwCommit

end Zcash.Snark.ZeroKnowledge
