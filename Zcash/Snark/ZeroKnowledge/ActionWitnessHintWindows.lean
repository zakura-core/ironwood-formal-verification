import Zcash.Snark.ZeroKnowledge.ActionWitnessHints

/-!
# Exact scalar windows from the fixed Action hint program

These are the values produced by the existing 85-window witness programs,
before any advice assignment is assumed. The field-to-Nat decoding theorem and
the base-eight reconstruction theorem recover each application scalar exactly.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Ecc.MulFixed.FullWidth

/-- Evaluate all 85 of the existing full-width gadget's scalar-window programs. -/
def actionScalarWindowValues (program : Var UnconstrainedNat Fp)
    (environment : Placed ProverEnvironment Fp) : Vector Fp 85 :=
  Vector.ofFn (fun window => Witgen.MOver.eval (value := field) environment (scalarWindows program)[window.val])

/-- Each existing window program computes the corresponding three bits of the decoded Nat. -/
theorem actionScalarWindowValues_digit (program : Var UnconstrainedNat Fp)
    (environment : Placed ProverEnvironment Fp) (window : Fin 85) :
    (actionScalarWindowValues program environment)[window.val] =
      (((Witgen.MOver.evalNat environment program >>> (3 * window.val)) &&& 7 : ℕ) : Fp) := by
  simp only [actionScalarWindowValues, Vector.getElem_ofFn]
  simp only [scalarWindows, Vector.getElem_ofFn]
  simp only [Witgen.MOver.eval, Witgen.MOver.evalNat, circuit_norm, Witgen.eval_field,
    Witgen.FExprOver.eval, Witgen.NExprOver.eval, FiniteField.fromNat_F]

/-- A scalar's exact Nat decoding makes the actual window programs equal its canonical digits. -/
theorem actionScalarWindowValues_canonical (program : Var UnconstrainedNat Fp)
    (environment : Placed ProverEnvironment Fp) (scalar : Fq)
    (hdecode : Witgen.MOver.evalNat environment program = scalar.val) :
    actionScalarWindowValues program environment = canonicalActionScalarWindows scalar := by
  apply Vector.ext
  intro index hi
  rw [actionScalarWindowValues_digit program environment ⟨index, hi⟩, hdecode,
    ← octalDigit_eq_shift_mask]
  simp only [canonicalActionScalarWindows, Vector.getElem_ofFn]

/-- The circuit's scalar extractor applied to the actual hint-program values recovers the input scalar. -/
theorem actionScalarWindowValues_reconstruct (program : Var UnconstrainedNat Fp)
    (environment : Placed ProverEnvironment Fp) (scalar : Fq)
    (hdecode : Witgen.MOver.evalNat environment program = scalar.val) :
    windowsScalar (actionScalarWindowValues program environment) = scalar := by
  rw [actionScalarWindowValues_canonical program environment scalar hdecode,
    canonicalActionScalarWindows_reconstruct]

/-- All five fixed Action scalar programs generate exactly the normalized application's windows. -/
theorem actionWitnessHintWindows_canonical (witness : PrivateWitness)
    (bounds : ActionScalarHintBounds witness) (place : RegionIndex → ℕ) (environment : Environment Fp) :
    let penv := actionWitnessHintEnvironment witness place environment
    actionScalarWindowValues Circuit.hintWitnesses.rcv penv = canonicalActionScalarWindows witness.rcv.2 ∧
    actionScalarWindowValues Circuit.hintWitnesses.alpha penv = canonicalActionScalarWindows witness.alpha.2 ∧
    actionScalarWindowValues Circuit.hintWitnesses.rivk penv = canonicalActionScalarWindows witness.rivk.2 ∧
    actionScalarWindowValues Circuit.hintWitnesses.rcmOld penv = canonicalActionScalarWindows witness.rcmOld.2 ∧
    actionScalarWindowValues Circuit.hintWitnesses.rcmNew penv = canonicalActionScalarWindows witness.rcmNew.2 := by
  have hdecode := actionWitnessHints_decode witness bounds place environment
  refine ⟨actionScalarWindowValues_canonical _ _ _ ?_,
    actionScalarWindowValues_canonical _ _ _ ?_, actionScalarWindowValues_canonical _ _ _ ?_,
    actionScalarWindowValues_canonical _ _ _ ?_, actionScalarWindowValues_canonical _ _ _ ?_⟩
  · simpa only [Circuit.hintWitnesses, actionWitnessHintData, circuit_norm] using
      congrArg Circuit.PrivateInputs.ProverValue.rcv hdecode
  · simpa only [Circuit.hintWitnesses, actionWitnessHintData, circuit_norm] using
      congrArg Circuit.PrivateInputs.ProverValue.alpha hdecode
  · simpa only [Circuit.hintWitnesses, actionWitnessHintData, circuit_norm] using
      congrArg Circuit.PrivateInputs.ProverValue.rivk hdecode
  · simpa only [Circuit.hintWitnesses, actionWitnessHintData, circuit_norm] using
      congrArg Circuit.PrivateInputs.ProverValue.rcmOld hdecode
  · simpa only [Circuit.hintWitnesses, actionWitnessHintData, circuit_norm] using
      congrArg Circuit.PrivateInputs.ProverValue.rcmNew hdecode

end Zcash.Snark.ZeroKnowledge
