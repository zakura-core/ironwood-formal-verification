import Zcash.Snark.Fixtures.Prover.Replay
import Zcash.Snark.Fixtures.Prover.Pins
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
import Zcash.Snark.ZeroKnowledge.Zakura.Attempt

/-!
# Explicit execution checks for the Rust prover captures

The `Main.lean` runner checks both complete captured executions in
Lean CI. This module is compiled by `FixtureCheck`, outside the production import
root. The generic replay equality is proved in `Replay`; the runner compares
external captured data and introduces no native-decision axioms.

The Python step authenticates the compressed artifacts before unpacking them into
the ignored build directory. The independent Lean decoder then checks their wire
format. Expected Rust outputs are supplied only to the comparisons after replay.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp URS)
open Zcash.Snark Zcash.Snark.ZeroKnowledge

/-- A failed fixture comparison fails the check. -/
private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError ("prover capture mismatch: " ++ label))

/-- Identify the first differing emitted message without dumping the private fixture inputs. -/
private def checkMessages (label : String) (actual expected : List (TranscriptElt Fp VestaG)) : IO Unit := do
  ensure (label ++ " message count") (actual.length == expected.length)
  for i in [:actual.length] do
    unless decide (actual[i]? = expected[i]?) do
      throw (IO.userError s!"prover capture mismatch: {label}, message {i}")

/-- Exercise the actual comparison routine and require it to reject a tampered transcript. -/
private def expectMismatch (label : String) (check : IO Unit) : IO Unit := do
  let rejected ← try
    check
    pure false
  catch _ => pure true
  ensure (label ++ " was not rejected") rejected

/-- Commit all captured public rows and compare them to the existing captured verification key. -/
private def checkKeyRows {actions : ℕ}
    (vk : VerifyingKey (plonkProofShape actions 11) Fp VestaG) (inputs : CaptureInputs) : IO Unit := do
  let generators : Fin 2048 → VestaG := fun i => inputs.generators[i.val]?.getD 0
  for i in List.finRange 29 do
    let coefficients := rowCoefficients 11 (by decide) (inputFixed inputs i)
    ensure s!"fixed commitment {i.val}"
      (decide (commitPolynomial generators inputs.w coefficients 1 = vk.fixedCommitment i.val))
  for i in List.finRange 15 do
    let coefficients := rowCoefficients 11 (by decide) (inputSigma inputs i)
    ensure s!"permutation commitment {i.val}"
      (decide (commitPolynomial generators inputs.w coefficients 1 = vk.permutationCommonCommitment i))

/-- Check a real proof call against both its own captured outputs and the existing verifier anchor. -/
private def checkCase {actions : ℕ} (name : String)
    (vk : VerifyingKey (plonkProofShape actions 11) Fp VestaG)
    (generators : Fin 2048 → VestaG) (W U : VestaG) (publicInputs : List (List Fp))
    (initial : List (TranscriptElt Fp VestaG)) (ch : Challenges 11 Fp)
    (expected : ProofString (plonkProofShape actions 11) Fp VestaG) (mutate : Bool) : IO Unit := do
  let bytes ← IO.FS.readBinFile (".lake/build/prover-captures/" ++ name ++ ".bin")
  let capture ← match decodeCapture actions bytes with
    | .ok capture => pure capture
    | .error error => throw (IO.userError error)
  let inputs := capture.inputs
  ensure (name ++ " generators") (decide (inputs.generators.toList = List.ofFn generators))
  ensure (name ++ " W/U") (decide (inputs.w = W ∧ inputs.u = U))
  ensure (name ++ " public inputs") (decide (inputs.instances.toList.map Array.toList = publicInputs))
  ensure (name ++ " initialization") (decide (capture.initialization = initial))
  ensure (name ++ " public acceptance") (Zakura.acceptsPublicPrefix capture.initialization)
  ensure (name ++ " challenges") (decide (inputs.challenges.toList = plonkChallengeSequence ch))
  checkMessages (name ++ " verifier anchor") capture.messages (plonkAttemptTrace expected)
  IO.println (name ++ ": checking public-row commitments")
  (← IO.getStdout).flush
  checkKeyRows vk inputs
  IO.println (name ++ ": replaying the complete private tape")
  (← IO.getStdout).flush
  let proof := replayProof vk inputs
  let trace := plonkAttemptTrace proof
  checkMessages name trace capture.messages
  let attempt := (encodedPlonkAttempt (inputChallenges inputs, proof)).2
  ensure (name ++ " terminal result") (decide (attempt.status = .complete))
  ensure (name ++ " released outcome") (decide (Zakura.observeAttempt attempt = .proof attempt.proof))
  expectMismatch (name ++ " changed scalar") (checkMessages name
    (trace.set (trace.length - 1) (.scalar (proof.ipaF + 1))) capture.messages)
  expectMismatch (name ++ " reordered messages") (checkMessages name trace.reverse capture.messages)
  expectMismatch (name ++ " truncated messages") (checkMessages name trace.dropLast capture.messages)
  expectMismatch (name ++ " extra message") (checkMessages name (trace ++ [.scalar 0]) capture.messages)
  if mutate then
    IO.println (name ++ ": checking sensitivity to a changed raw RNG draw")
    (← IO.getStdout).flush
    let changed := { inputs with rawTape := inputs.rawTape.modify (inputs.rawTape.length - 1) (· + 1) }
    let changedTrace := plonkAttemptTrace (replayProof vk changed)
    expectMismatch (name ++ " changed raw draw") (checkMessages name changedTrace capture.messages)
  ensure (name ++ " truncated bytes rejected")
    (match decodeCapture actions (bytes.extract 0 (bytes.size - 1)) with | .error _ => true | .ok _ => false)
  IO.println (name ++ ": all messages, public anchors, outcome, and negative checks passed")
  (← IO.getStdout).flush

/-- Authenticate the pinned artifacts, then check the complete one- and two-Action executions. -/
def checkCaptures : IO Unit := do
  let checked ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/generate_prover_fixtures.py", "--check", "--extract", ".lake/build/prover-captures"] }
  unless checked.exitCode == 0 do throw (IO.userError (checked.stdout ++ checked.stderr))
  ensure "capture pin inventory" (capturePins.length == 2)
  checkCase "single-honest" Fixture.vk Fixture.capturedURS.g Fixture.capturedURS.w Fixture.capturedURS.u
    Fixture.capturedPublicInstances Fixture.capturedInit Fixture.ch Fixture.ps true
  checkCase "multi-honest" Fixture2.vk Fixture2.capturedURS.g Fixture2.capturedURS.w Fixture2.capturedURS.u
    Fixture2.capturedPublicInstances Fixture2.capturedInit Fixture2.ch Fixture2.ps false

end Zcash.Snark.Fixtures.Prover
