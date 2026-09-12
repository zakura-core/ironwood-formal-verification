import Zcash.Snark.ZeroKnowledge.ActionWitnessHintWindows

/-!
# Exact scalar extraction from the original full-width gadget

Every original window cell equals its supplied window program whenever the
original call's witness equations hold. Exact Nat decoding then recovers both
the canonical window vector and the application scalar, including the highest
allowed bits. No gate-validity or successful-output assumption is used.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Ecc.MulFixed.FullWidth
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] witnessScalarLoop innerRegion synthesize circuit

/-- The original scalar loop writes exactly the supplied window-program values. -/
theorem fullWidth_windowCells_of_witnessScalarLoop
    (cfg : Config) (offset self : ℕ) (env : Placed ProverEnvironment Fp)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      ((witnessScalarLoop cfg windows offset).operations self)) :
    @Eval.eval _ _ _ (CircuitType.verifierEval (fields 85))
      (⟨env.place, env.env.toEnvironment⟩ : Placed Environment Fp) (windowCells cfg offset self) =
      Vector.ofFn (fun w : Fin 85 => Witgen.MOver.eval (value := field) env (windows[w.val]'w.isLt)) := by
  simp only [witnessScalarLoop, circuit_norm, mul_one] at hw
  apply Vector.ext
  intro index hi
  simp only [windowCells, circuit_norm, Vector.getElem_ofFn, AssignedCell.eval,
    AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
    Environment.get_advice]
  have h := hw ⟨index, hi⟩
  with_unfolding_all
    change env.env.advice cfg.superConfig.window ↑(env.place self + (offset + index)) =
      Witgen.MOver.eval (value := field) env windows[index]! at h
  rw [getElem!_pos windows index hi] at h
  simpa only [circuit_norm] using h

/-- The actual full-width call's extraction recovers its window-program values. -/
theorem fullWidth_extract_windows_of_extendsWitnesses
    (base : Ecc.MulFixed.FixedBase) (cfg : Config)
    (scalar : Var UnconstrainedNat Fp) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env
      (((circuit base).call cfg scalar).operations self) self) :
    (fwExtract cfg self ⟨env.place, env.env.toEnvironment⟩).1 =
      actionScalarWindowValues scalar env := by
  rw [FormalCircuit.call_operations] at hw
  with_unfolding_all
    change ExtendsWitnesses env.place env.env
      ((synthesize base.toData cfg (scalarWindows scalar)).operations self) self at hw
  simp only [synthesize, Circuit.operations_bind, operations_assignRegion, circuit_norm] at hw
  have hwInner := hw.1
  rw [innerRegion_operations_eq] at hwInner
  simp only [RegionOperations.extendsWitnesses_append] at hwInner
  exact fullWidth_windowCells_of_witnessScalarLoop cfg 0 self env _ hwInner.1.1

/-- Exact Nat decoding and witness consistency recover the semantic application scalar. -/
theorem fullWidth_extract_scalar_of_extendsWitnesses
    (base : Ecc.MulFixed.FixedBase) (cfg : Config)
    (program : Var UnconstrainedNat Fp) (self : ℕ) (env : Placed ProverEnvironment Fp)
    (scalar : Fq) (hdecode : Witgen.MOver.evalNat env program = scalar.val)
    (hw : ExtendsWitnesses env.place env.env
      (((circuit base).call cfg program).operations self) self) :
    fwExtract cfg self ⟨env.place, env.env.toEnvironment⟩ =
      (canonicalActionScalarWindows scalar, scalar) := by
  have hwindows := fullWidth_extract_windows_of_extendsWitnesses base cfg program self env hw
  have hcanonical := hwindows.trans (actionScalarWindowValues_canonical program env scalar hdecode)
  apply Prod.ext
  · exact hcanonical
  · change windowsScalar (fwExtract cfg self ⟨env.place, env.env.toEnvironment⟩).1 = scalar
    rw [hcanonical, canonicalActionScalarWindows_reconstruct]
end Zcash.Snark.ZeroKnowledge
