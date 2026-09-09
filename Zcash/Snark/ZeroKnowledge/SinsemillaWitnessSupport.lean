import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.Sinsemilla.HashToPoint

/-!
# Read certificates for original Sinsemilla native callbacks

State steps read the previous row and piece cell. The initial virtual-y input
retains its own support, and boundary-y derivation is certified from the exact
preceding row and next x cell. Fixed generators introduce no environment read.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits

/-- The original Sinsemilla state evaluator's five source cells. -/
def sinsemillaStateReads (state : Sinsemilla.HashPiece.State (AssignedCell Fp)) : List (AssignedCell Fp) :=
  [state.z, state.row.xA, state.row.xP, state.row.lambda1, state.row.lambda2]

/-- The complete entering state is determined by those five cells. -/
theorem sinsemilla_readsValue_support (state : Sinsemilla.HashPiece.State (AssignedCell Fp)) :
    WitnessFunctionSupport (sinsemillaStateReads state) (Sinsemilla.HashPiece.readsValue state) := by
  intro left right agreement
  have hz : Sinsemilla.HashPiece.readCell left state.z = Sinsemilla.HashPiece.readCell right state.z :=
    agreement.cellValues state.z (by simp [sinsemillaStateReads])
  have ha : Sinsemilla.HashPiece.readCell left state.row.xA = Sinsemilla.HashPiece.readCell right state.row.xA :=
    agreement.cellValues state.row.xA (by simp [sinsemillaStateReads])
  have hp : Sinsemilla.HashPiece.readCell left state.row.xP = Sinsemilla.HashPiece.readCell right state.row.xP :=
    agreement.cellValues state.row.xP (by simp [sinsemillaStateReads])
  have h1 : Sinsemilla.HashPiece.readCell left state.row.lambda1 =
      Sinsemilla.HashPiece.readCell right state.row.lambda1 :=
    agreement.cellValues state.row.lambda1 (by simp [sinsemillaStateReads])
  have h2 : Sinsemilla.HashPiece.readCell left state.row.lambda2 =
      Sinsemilla.HashPiece.readCell right state.row.lambda2 :=
    agreement.cellValues state.row.lambda2 (by simp [sinsemillaStateReads])
  simp only [Sinsemilla.HashPiece.readsValue, hz, ha, hp, h1, h2]

/-- The first generator-coordinate witness reads just the piece cell. -/
theorem sinsemilla_initXPWit_support (generators : Specs.Sinsemilla.Generators) (piece : AssignedCell Fp) :
    WitnessFunctionSupport [piece] (fun env => ((Sinsemilla.HashPiece.initXPWit generators piece).eval env)[0]) := by
  intro left right agreement
  have hp := agreement.cellValues piece (List.mem_singleton_self _)
  simpa only [Sinsemilla.HashPiece.initXPWit_eval] using
    congrArg (fun value => (generators.S (Sinsemilla.pieceWord value 0)).x) hp

/-- An original state-step callback reads its entering state and piece cell. -/
theorem sinsemilla_stepWit_support (generators : Specs.Sinsemilla.Generators)
    (piece : AssignedCell Fp) (state : Sinsemilla.HashPiece.State (AssignedCell Fp)) (word : ℕ)
    (f : Sinsemilla.HashPiece.State Fp → Fp) :
    WitnessFunctionSupport (sinsemillaStateReads state ++ [piece])
      (fun env => ((Sinsemilla.HashPiece.stepWit generators piece state word f).eval env)[0]) := by
  intro left right agreement
  have hs := sinsemilla_readsValue_support state left right agreement.left
  have hp : piece.eval left.place left.env.toEnvironment = piece.eval right.place right.env.toEnvironment :=
    agreement.right.cellValues piece (List.mem_singleton_self _)
  simp only [Sinsemilla.HashPiece.stepWit_eval, hs, hp]

/-- The exit x-coordinate is a deterministic function of the original entering state. -/
theorem sinsemilla_exitXAWit_support (state : Sinsemilla.HashPiece.State (AssignedCell Fp)) :
    WitnessFunctionSupport (sinsemillaStateReads state)
      (fun env => ((Sinsemilla.HashPiece.exitXAWit state).eval env)[0]) := by
  intro left right agreement
  simp only [Sinsemilla.HashPiece.exitXAWit_eval,
    sinsemilla_readsValue_support state left right agreement]

/-- The initial slopes retain every read of their virtual-y input. -/
theorem sinsemilla_initLWit_support (generators : Specs.Sinsemilla.Generators)
    (piece x : AssignedCell Fp) (y : Placed Environment Fp → Fp)
    (f : Fp × Fp × (Fp × Fp) → Fp) (reads : List (AssignedCell Fp))
    (hy : WitnessFunctionSupport reads (fun env => y env.toEnvironment)) :
    WitnessFunctionSupport ([piece, x] ++ reads)
      (fun env => ((Sinsemilla.HashPiece.initLWit generators piece x y f).eval env)[0]) := by
  intro left right agreement
  have hp : piece.eval left.place left.env.toEnvironment = piece.eval right.place right.env.toEnvironment :=
    agreement.left.cellValues piece (by simp)
  have hx : x.eval left.place left.env.toEnvironment = x.eval right.place right.env.toEnvironment :=
    agreement.left.cellValues x (by simp)
  have hy' := hy left right agreement.right
  simp only [Sinsemilla.HashPiece.initLWit_eval, hp, hx, hy']

/-- The virtual boundary-y value reads four preceding row cells and the next x cell. -/
theorem sinsemilla_boundaryYA_support (last : Ecc.DoubleAndAddRow (AssignedCell Fp))
    (nextX : AssignedCell Fp) :
    WitnessFunctionSupport [last.xA, last.xP, last.lambda1, last.lambda2, nextX]
      (fun env => Sinsemilla.Chain.boundaryYA last nextX env.toEnvironment) := by
  intro left right agreement
  have ha : last.xA.eval left.place left.env.toEnvironment = last.xA.eval right.place right.env.toEnvironment :=
    agreement.cellValues last.xA (by simp)
  have hp : last.xP.eval left.place left.env.toEnvironment = last.xP.eval right.place right.env.toEnvironment :=
    agreement.cellValues last.xP (by simp)
  have h1 : last.lambda1.eval left.place left.env.toEnvironment =
      last.lambda1.eval right.place right.env.toEnvironment := agreement.cellValues last.lambda1 (by simp)
  have h2 : last.lambda2.eval left.place left.env.toEnvironment =
      last.lambda2.eval right.place right.env.toEnvironment := agreement.cellValues last.lambda2 (by simp)
  have hn : nextX.eval left.place left.env.toEnvironment = nextX.eval right.place right.env.toEnvironment :=
    agreement.cellValues nextX (by simp)
  simp only [Sinsemilla.Chain.boundaryYA, Placed.toEnvironment, ha, hp, h1, h2, hn]

/-- The original trailing y witness uses exactly the certified boundary computation. -/
theorem sinsemilla_finalYAWit_support (last : Ecc.DoubleAndAddRow (AssignedCell Fp))
    (nextX : AssignedCell Fp) :
    WitnessFunctionSupport [last.xA, last.xP, last.lambda1, last.lambda2, nextX]
      (fun env => ((Sinsemilla.Chain.finalYAWit last nextX).eval env)[0]) := by
  intro left right agreement
  simpa only [Sinsemilla.Chain.finalYAWit_eval] using sinsemilla_boundaryYA_support last nextX left right agreement

/-- The dummy-row zero witness reads no cell. -/
theorem sinsemilla_zeroWit_support :
    WitnessFunctionSupport [] (fun env => (Sinsemilla.Chain.zeroWit.eval env)[0]) := by
  intro left right _
  simp only [Sinsemilla.Chain.zeroWit_eval]

/-- The original initial-point constant witness reads no cell. -/
theorem sinsemilla_constWit_support (value : Fp) :
    WitnessFunctionSupport [] (fun env => ((Sinsemilla.HashToPoint.constWit value).eval env)[0]) := by
  intro left right _
  rfl

end Zcash.Snark.ZeroKnowledge
