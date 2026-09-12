/-!
# Data exported from selected Rust prover calls

Generated fixtures retain natural-number representatives and event order. The
decoder checks their field ranges, curve equations, dimensions, and successful
call boundaries before constructing the replay inputs.
-/

namespace Zcash.Snark.Fixtures.Prover

/-- Coordinates retain their original representatives until the decoder checks Vesta membership. -/
inductive FixturePoint where
  | identity
  | affine (x y : Nat)
  deriving DecidableEq

/-- Public transcript initialization records the values actually absorbed by Rust. -/
inductive FixtureMessage where
  | point (value : FixturePoint)
  | scalar (value : Nat)
  deriving DecidableEq

/-- The successful profile retains every u64 RNG call and transcript operation in order. -/
inductive FixtureEvent where
  | rng64 (value : Nat)
  | point (value : FixturePoint)
  | scalar (value : Nat)
  | challenge (value : Nat)
  | success
  deriving DecidableEq

/-- Public setup is checked against the existing verifier fixtures before replay. -/
structure FixtureSetup where
  k : Nat
  rows : Nat
  blindingFactors : Nat
  degree : Nat
  generators : Array FixturePoint
  w : FixturePoint
  u : FixturePoint
  fixed : Array (Array Nat)
  sigma : Array (Array Nat)

/-- A generated call stores Rust-synthesized rows, public inputs, and the recorded execution. -/
structure ProverFixture where
  setup : FixtureSetup
  instances : Array (Array Nat)
  witness : Array (Array (Array Nat))
  initialization : Array FixtureMessage
  events : Array FixtureEvent
  proof : Array Nat

end Zcash.Snark.Fixtures.Prover
