import Zcash.Snark.ZeroKnowledge.ActionWitnessConditions

/-!
# Encoding application witnesses for the fixed Action hint program

The stored values are ordinary field arrays under the keys used by
`Circuit.hintWitnesses`. Scalar decoding uses the existing field-to-Nat bridge;
its representability conditions are explicit. The encoding does not consult any
advice assignment, proof, or verifier result.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2
open Zcash.Circuits
open Zcash.Circuits.Action
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- The prover data derived directly from an application witness. -/
def actionWitnessHintData (witness : PrivateWitness) : Circuit.WitnessData Fp := {
  psiOld := witness.psiOld
  rhoOld := witness.rhoOld
  nk := witness.nk
  vOld := witness.vOld
  vNew := witness.vNew
  psiNew := witness.psiNew
  magnitude := witness.magnitude
  sign := witness.sign
  cmOld := witness.cmOld
  gdOld := witness.gdOld
  akP := witness.akP
  pkDOld := witness.pkdOld
  gdNew := witness.gdNew
  pkdNew := witness.pkdNew
  rcv := witness.rcv.2.val
  alpha := witness.alpha.2.val
  rivk := witness.rivk.2.val
  rcmOld := witness.rcmOld.2.val
  rcmNew := witness.rcmNew.2.val
  merkleSib := fun layer => (canonicalActionMerklePath witness layer).1
  merkleSwap := actionWitnessSide witness
}

/-- Field-array storage consumed by the existing fixed top-level Action hint program. -/
def actionWitnessHints (witness : PrivateWitness) : ProverHint Fp := fun key width =>
  match key with
  | "orchard.action.psi_old" => #[Vector.replicate width witness.psiOld]
  | "orchard.action.rho_old" => #[Vector.replicate width witness.rhoOld]
  | "orchard.action.nk" => #[Vector.replicate width witness.nk]
  | "orchard.action.v_old" => #[Vector.replicate width witness.vOld]
  | "orchard.action.v_new" => #[Vector.replicate width witness.vNew]
  | "orchard.action.psi_new" => #[Vector.replicate width witness.psiNew]
  | "orchard.action.magnitude" => #[Vector.replicate width witness.magnitude]
  | "orchard.action.sign" => #[Vector.replicate width witness.sign]
  | "orchard.action.cm_old" => #[Vector.ofFn (fun col => if col.val = 0 then witness.cmOld.x else if col.val = 1 then witness.cmOld.y else 0)]
  | "orchard.action.gd_old" => #[Vector.ofFn (fun col => if col.val = 0 then witness.gdOld.x else if col.val = 1 then witness.gdOld.y else 0)]
  | "orchard.action.ak_p" => #[Vector.ofFn (fun col => if col.val = 0 then witness.akP.x else if col.val = 1 then witness.akP.y else 0)]
  | "orchard.action.pkd_old" => #[Vector.ofFn (fun col => if col.val = 0 then witness.pkdOld.x else if col.val = 1 then witness.pkdOld.y else 0)]
  | "orchard.action.gd_new" => #[Vector.ofFn (fun col => if col.val = 0 then witness.gdNew.x else if col.val = 1 then witness.gdNew.y else 0)]
  | "orchard.action.pkd_new" => #[Vector.ofFn (fun col => if col.val = 0 then witness.pkdNew.x else if col.val = 1 then witness.pkdNew.y else 0)]
  | "orchard.action.rcv" => #[Vector.replicate width (witness.rcv.2.val : Fp)]
  | "orchard.action.alpha" => #[Vector.replicate width (witness.alpha.2.val : Fp)]
  | "orchard.action.rivk" => #[Vector.replicate width (witness.rivk.2.val : Fp)]
  | "orchard.action.rcm_old" => #[Vector.replicate width (witness.rcmOld.2.val : Fp)]
  | "orchard.action.rcm_new" => #[Vector.replicate width (witness.rcmNew.2.val : Fp)]
  | "orchard.action.merkle_sibling" =>
      Array.ofFn (fun layer : Fin 32 => Vector.replicate width (canonicalActionMerklePath witness layer.val).1)
  | "orchard.action.merkle_swap" =>
      Array.ofFn (fun layer : Fin 32 => Vector.replicate width (if witness.merkleSide layer then 1 else 0))
  | _ => #[]

/-- Install the application hints while leaving placement and circuit cells available to the witness program. -/
def actionWitnessHintEnvironment (witness : PrivateWitness) (place : RegionIndex → ℕ)
    (environment : Environment Fp) : Placed ProverEnvironment Fp :=
  ⟨place, { environment with hint := actionWitnessHints witness }⟩

/-- Every sibling read, including padding beyond the 32 layers, matches the canonical path. -/
theorem actionWitnessHints_sibling_read (witness : PrivateWitness) (layer : ℕ) :
    ((actionWitnessHints witness "orchard.action.merkle_sibling" 1)[layer]?.getD default)[0] =
      (canonicalActionMerklePath witness layer).1 := by
  by_cases hi : layer < 32
  · simp [actionWitnessHints, hi]
  · simp [actionWitnessHints, canonicalActionMerklePath, hi]
    rfl

/-- The stored Boolean field flag decodes to the application's side choice, with false padding. -/
theorem actionWitnessHints_swap_read (witness : PrivateWitness) (layer : ℕ) :
    (((actionWitnessHints witness "orchard.action.merkle_swap" 1)[layer]?.getD default)[0] == 1) =
      actionWitnessSide witness layer := by
  by_cases hi : layer < 32
  · cases hs : witness.merkleSide ⟨layer, hi⟩ <;>
      simp [actionWitnessHints, actionWitnessSide, hi, hs]
  · simp [actionWitnessHints, actionWitnessSide, hi]
    exact zero_ne_one

/-- Evaluate the two coordinate reads of a point hint without assuming any advice cells. -/
theorem actionPointHint_eval (environment : Placed ProverEnvironment Fp) (key : String) :
    Witgen.eval { env := environment }
      (⟨.hintGet key 2 (.const 0) 0, .hintGet key 2 (.const 0) 1⟩ : Point (FExpr Fp)) =
      (⟨((environment.env.hint key 2)[0]?.getD default)[0],
        ((environment.env.hint key 2)[0]?.getD default)[1]⟩ : Point Fp) := by
  simp [Witgen.eval, ProvableType.toElements, ProvableType.fromElements,
    Witgen.FExprOver.eval, Witgen.NExprOver.eval]
  exact ⟨rfl, rfl⟩

/-- The sibling input's prover evaluation runs the stored one-field program at the requested layer. -/
theorem actionMerkleSibling_eval (environment : Placed ProverEnvironment Fp)
    (programs : ℕ → WitgenIR Fp 1) (layer : ℕ) :
    @Eval.eval _ _ _ (CircuitType.proverEval Circuit.UnconstrainedSibs) environment programs layer =
      ((programs layer).eval environment)[0] := by
  with_unfolding_all rfl

/-- The swap input's prover evaluation invokes its actual Boolean reading function. -/
theorem actionMerkleSwap_eval (environment : Placed ProverEnvironment Fp)
    (flags : ℕ → Placed ProverEnvironment Fp → Bool) (layer : ℕ) :
    @Eval.eval _ _ _ (CircuitType.proverEval Circuit.UnconstrainedSwaps) environment flags layer =
      flags layer environment := by
  with_unfolding_all rfl

/-- The fixed top-level hint program decodes the supplied application data in every cell environment. -/
theorem actionWitnessHints_decode (witness : PrivateWitness)
    (bounds : ActionScalarHintBounds witness) (place : RegionIndex → ℕ) (environment : Environment Fp) :
    @Eval.eval _ _ _ (CircuitType.proverEval Circuit.PrivateInputs)
      (actionWitnessHintEnvironment witness place environment) Circuit.hintWitnesses = actionWitnessHintData witness := by
  simp only [Circuit.hintWitnesses, actionWitnessHintData, circuit_norm]
  have scalarDecode (scalar : Fq) (hbound : scalar.val < PALLAS_BASE_CARD) :
      ((scalar.val : ℕ) : Fp).val = scalar.val := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hbound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change witness.psiOld = witness.psiOld
    rfl
  · change witness.rhoOld = witness.rhoOld
    rfl
  · change witness.nk = witness.nk
    rfl
  · change witness.vOld = witness.vOld
    rfl
  · change witness.vNew = witness.vNew
    rfl
  · change witness.psiNew = witness.psiNew
    rfl
  · change witness.magnitude = witness.magnitude
    rfl
  · change witness.sign = witness.sign
    rfl
  · change Witgen.eval { env := actionWitnessHintEnvironment witness place environment }
        (⟨.hintGet "orchard.action.cm_old" 2 (.const 0) 0,
          .hintGet "orchard.action.cm_old" 2 (.const 0) 1⟩ : Point (FExpr Fp)) = witness.cmOld
    rw [actionPointHint_eval]
    simp [actionWitnessHintEnvironment, actionWitnessHints]
  · change Witgen.eval { env := actionWitnessHintEnvironment witness place environment }
        (⟨.hintGet "orchard.action.gd_old" 2 (.const 0) 0,
          .hintGet "orchard.action.gd_old" 2 (.const 0) 1⟩ : Point (FExpr Fp)) = witness.gdOld
    rw [actionPointHint_eval]
    simp [actionWitnessHintEnvironment, actionWitnessHints]
  · change Witgen.eval { env := actionWitnessHintEnvironment witness place environment }
        (⟨.hintGet "orchard.action.ak_p" 2 (.const 0) 0,
          .hintGet "orchard.action.ak_p" 2 (.const 0) 1⟩ : Point (FExpr Fp)) = witness.akP
    rw [actionPointHint_eval]
    simp [actionWitnessHintEnvironment, actionWitnessHints]
  · change Witgen.eval { env := actionWitnessHintEnvironment witness place environment }
        (⟨.hintGet "orchard.action.pkd_old" 2 (.const 0) 0,
          .hintGet "orchard.action.pkd_old" 2 (.const 0) 1⟩ : Point (FExpr Fp)) = witness.pkdOld
    rw [actionPointHint_eval]
    simp [actionWitnessHintEnvironment, actionWitnessHints]
  · change Witgen.eval { env := actionWitnessHintEnvironment witness place environment }
        (⟨.hintGet "orchard.action.gd_new" 2 (.const 0) 0,
          .hintGet "orchard.action.gd_new" 2 (.const 0) 1⟩ : Point (FExpr Fp)) = witness.gdNew
    rw [actionPointHint_eval]
    simp [actionWitnessHintEnvironment, actionWitnessHints]
  · change Witgen.eval { env := actionWitnessHintEnvironment witness place environment }
        (⟨.hintGet "orchard.action.pkd_new" 2 (.const 0) 0,
          .hintGet "orchard.action.pkd_new" 2 (.const 0) 1⟩ : Point (FExpr Fp)) = witness.pkdNew
    rw [actionPointHint_eval]
    simp [actionWitnessHintEnvironment, actionWitnessHints]
  · exact scalarDecode witness.rcv.2 bounds.rcv
  · exact scalarDecode witness.alpha.2 bounds.alpha
  · exact scalarDecode witness.rivk.2 bounds.rivk
  · exact scalarDecode witness.rcmOld.2 bounds.rcmOld
  · exact scalarDecode witness.rcmNew.2 bounds.rcmNew
  · funext layer
    rw [actionMerkleSibling_eval]
    change ((Witgen.WitgenIROver.ofFExpr
      (.hintGet "orchard.action.merkle_sibling" 1 (.const layer) 0) : WitgenIR Fp 1).eval
      (actionWitnessHintEnvironment witness place environment))[0] = _
    rw [Halo2.eval_ofFExpr_zero]
    exact actionWitnessHints_sibling_read witness layer
  · funext layer
    rw [actionMerkleSwap_eval]
    exact actionWitnessHints_swap_read witness layer

end Zcash.Snark.ZeroKnowledge
