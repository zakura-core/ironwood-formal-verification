import Zcash.Snark.Fixtures.Prover.Capture
import Zcash.Snark.Fixtures.Prover.Execution
import Zcash.Snark.ZeroKnowledge.PlonkChallenges

/-!
# Replaying decoded Rust inputs

Only `CaptureInputs` crosses this boundary. Expected commitments, evaluations, and
terminal results remain in the separate `Capture` record used by the checks.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp URS)
open Zcash.Snark Zcash.Snark.ZeroKnowledge

/-- The captured public column uses the prover's zero padding after its ten supplied values. -/
def inputInstances {actions : ℕ} (inputs : CaptureInputs) : Fin actions → Fin 2048 → Fp :=
  fun a row => (inputs.instances[a.val]?.getD #[])[row.val]?.getD 0

/-- Read the complete captured fixed rows in column-major order. -/
def inputFixed (inputs : CaptureInputs) : Fin 29 → Fin 2048 → Fp :=
  fun c row => (inputs.fixed[c.val]?.getD #[])[row.val]?.getD 0

/-- Read the complete captured permutation mapping in column-major order. -/
def inputSigma (inputs : CaptureInputs) : Fin 15 → Fin 2048 → Fp :=
  fun c row => (inputs.sigma[c.val]?.getD #[])[row.val]?.getD 0

/-- Read the ten synthesized advice columns before any prover tail is randomized. -/
def inputWitness {actions : ℕ} (inputs : CaptureInputs) : Fin actions → Fin 10 → Fin 2048 → Fp :=
  fun a c row => ((inputs.witness[a.val]?.getD #[])[c.val]?.getD #[])[row.val]?.getD 0

/-- The actual received challenges occupy the reference model's exact typed positions. -/
def inputChallenges (inputs : CaptureInputs) : Challenges 11 Fp :=
  plonkChallengesFromTape (fun i => inputs.challenges[i.val]?.getD 0)

/-- Recompute the proof using only captured inputs, with the specified reduction of every raw word. -/
def replayProof {actions : ℕ} (vk : VerifyingKey (plonkProofShape actions 11) Fp VestaG)
    (inputs : CaptureInputs) : ProofString (plonkProofShape actions 11) Fp VestaG :=
  let words := inputs.rawTape.toArray
  let fields := cacheFn (reduceFieldTape (count := fieldSampleCount actions)
    (fun i => words[i.val]?.getD 0))
  execute (fun i => inputs.generators[i.val]?.getD 0) inputs.w inputs.u vk
    (inputInstances inputs) (inputFixed inputs) (inputSigma inputs) (inputWitness inputs)
    (inputChallenges inputs) fields.get

/-- **Prover replay.** Decoded inputs produce the full fixed-tape reference prover's proof. -/
theorem replay_eq_reference_capstone {actions : ℕ}
    (vk : VerifyingKey (plonkProofShape actions 11) Fp VestaG) (inputs : CaptureInputs) :
    replayProof vk inputs =
      plonkReferenceProofFromTape
        (⟨11, fun i => inputs.generators[i.val]?.getD 0, inputs.w, inputs.u⟩ : URS VestaG) rfl vk
        (plonkPublicPolynomialsFromRows (inputInstances inputs) (inputFixed inputs) (inputSigma inputs))
        (inputWitness inputs) (inputChallenges inputs)
        (reduceFieldTape (fun i => inputs.rawTape.getD i.val 0)) := by
  simp only [replayProof, cacheFn_result, execute_result, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

end Zcash.Snark.Fixtures.Prover
