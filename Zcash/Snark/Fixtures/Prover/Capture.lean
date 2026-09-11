import Zcash.Snark.Fixtures.Prover.FixtureData
import Zcash.Snark.Core.Vesta
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.ZeroKnowledge.RawFieldTape

/-!
# Checking the Rust-exported Lean prover fixtures

The fixtures store the original natural-number representatives and call order.
This decoder independently checks field ranges, curve membership, dimensions,
RNG counts at challenge boundaries, and terminal success before replay.
Expected transcript messages remain separate from the replay's inputs.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Snark.ZeroKnowledge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

/-- Private inputs and public setup captured before the prover randomizes witness tails. -/
structure CaptureInputs where
  actions : ℕ
  generators : Array VestaG
  w : VestaG
  u : VestaG
  fixed : Array (Array Fp)
  sigma : Array (Array Fp)
  instances : Array (Array Fp)
  witness : Array (Array (Array Fp))
  rawTape : List (Fin challengeDigestCard)
  challenges : Array Fp

/-- Outputs are stored separately so replay cannot use the messages it must reproduce. -/
structure Capture where
  inputs : CaptureInputs
  initialization : List (TranscriptElt Fp VestaG)
  messages : List (TranscriptElt Fp VestaG)
  proof : List UInt8

/-- A scalar must retain its canonical representative rather than silently reducing modulo p. -/
private def fieldValue (value : Nat) : Except String Fp :=
  if value < scalarFieldOrder then .ok (value : Fp) else .error "noncanonical scalar"

/-- A captured point must have canonical coordinates satisfying Vesta's curve equation. -/
private def pointValue : FixturePoint → Except String VestaG
  | .identity => .ok 0
  | .affine x y => do
    unless x < PALLAS_SCALAR_CARD ∧ y < PALLAS_SCALAR_CARD do
      throw "noncanonical point coordinate"
    let x : VestaBaseField := x
    let y : VestaBaseField := y
    if h : OnCurve Vesta.a Vesta.b (x, y) then return ⟨x, y, Or.inl h⟩
    else throw "point is not on Vesta"

/-- Successful transcript operations cannot contain identity points. -/
private def successfulPoint (value : FixturePoint) : Except String VestaG := do
  let point ← pointValue value
  if point = 0 then throw "identity in a successful transcript"
  return point

/-- Required dimensions exclude missing values before row readers can use zero padding. -/
private def fieldValues (size : Nat) (values : Array Nat) : Except String (Array Fp) := do
  unless values.size == size do throw "unsupported field-vector dimension"
  values.mapM fieldValue

/-- Column-major matrices include every row of the released domain. -/
private def matrixValues (columns : Nat) (values : Array (Array Nat)) :
    Except String (Array (Array Fp)) := do
  unless values.size == columns do throw "unsupported column count"
  values.mapM (fieldValues 2048)

/-- Exactly eight original u64 results form each bounded little-endian 512-bit raw word. -/
private def packWords (words : Array Nat) : Except String (List (Fin challengeDigestCard)) := do
  unless words.size % 8 == 0 do throw "incomplete wide RNG draw"
  let mut result := #[]
  for index in [:words.size / 8] do
    let value := (words.extract (8 * index) (8 * (index + 1))).foldr
      (fun word rest => word + 2 ^ 64 * rest) 0
    if h : value < challengeDigestCard then result := result.push ⟨value, h⟩
    else throw "wide RNG word exceeds 512 bits"
  return result.toList

/-- Stage boundaries include discarded tail draws and the final IPA masks. -/
def challengeDrawCounts (actions : Nat) : List Nat :=
  ([70 * actions, 112 * actions, 112 * actions,
    148 * actions + 3, 148 * actions + 11, 148 * actions + 11, 148 * actions + 11,
    148 * actions + 12, 148 * actions + 12, 148 * actions + 24, 148 * actions + 24] ++
    (List.range 11).map (fun round => 148 * actions + 26 + 2 * round)).map (8 * ·)

/-- Validate one complete Rust-exported Lean fixture before separating inputs from outputs. -/
def decodeCapture (actions : Nat) (fixture : ProverFixture) : Except String Capture := do
  unless actions == 1 || actions == 2 do throw "unsupported Action count"
  let setup := fixture.setup
  unless setup.k == 11 && setup.rows == 2048 && setup.blindingFactors == 5 && setup.degree == 9 do
    throw "unsupported prover setup"
  unless setup.generators.size == 2048 do throw "wrong generator count"
  let generators ← setup.generators.mapM pointValue
  let w ← pointValue setup.w
  let u ← pointValue setup.u
  let fixed ← matrixValues 29 setup.fixed
  let sigma ← matrixValues 15 setup.sigma
  unless fixture.instances.size == actions && fixture.witness.size == actions do
    throw "Action count mismatch"
  let instances ← fixture.instances.mapM (fieldValues 10)
  let witness ← fixture.witness.mapM (matrixValues 10)
  unless fixture.initialization.size == 1 + actions do throw "incomplete initialization"
  let some (FixtureMessage.scalar initial) := fixture.initialization[0]? | throw "missing initial scalar"
  let mut initialization := [TranscriptElt.scalar (← fieldValue initial)]
  for message in fixture.initialization.extract 1 fixture.initialization.size do
    let .point value := message | throw "expected instance commitment"
    initialization := initialization ++ [.point (← successfulPoint value)]
  unless fixture.events.size ≤ 4096 do throw "too many captured events"
  unless fixture.events.back? = some .success do throw "missing terminal success"
  let mut words := #[]
  let mut challenges := #[]
  let mut boundaries := #[]
  let mut messages := #[]
  let mut points := 0
  let mut scalars := 0
  for event in fixture.events.extract 0 (fixture.events.size - 1) do
    match event with
    | .rng64 word =>
      unless word < 2 ^ 64 do throw "RNG word exceeds 64 bits"
      words := words.push word
    | .point value =>
      messages := messages.push (.point (← successfulPoint value))
      points := points + 1
    | .scalar value =>
      messages := messages.push (.scalar (← fieldValue value))
      scalars := scalars + 1
    | .challenge value =>
      challenges := challenges.push (← fieldValue value)
      boundaries := boundaries.push words.size
      messages := messages.push .challenge
    | .success => throw "early terminal success"
  unless words.size == 8 * (148 * actions + 46) do throw "wrong RNG draw count"
  unless boundaries.toList == challengeDrawCounts actions do throw "RNG stage boundary mismatch"
  unless points == 22 * actions + 33 && scalars == 49 * actions + 52 do
    throw "incomplete prover message inventory"
  unless fixture.proof.size == 2720 + 2272 * actions do throw "wrong proof buffer length"
  let proof ← fixture.proof.toList.mapM fun byte => do
    unless byte < 256 do throw "proof byte exceeds 8 bits"
    return UInt8.ofNat byte
  let rawTape ← packWords words
  return {
    inputs := ⟨actions, generators, w, u, fixed, sigma, instances, witness, rawTape, challenges⟩
    initialization := initialization
    messages := messages.toList
    proof := proof }

end Zcash.Snark.Fixtures.Prover
