import Zcash.Snark.Fixtures.Prover.Check

/-!
# Running the captured prover executions

`lake env lean --run Zcash/Snark/Fixtures/Prover/Main.lean` runs the checks after
the default build, including when build artifacts are cached. The interpreter
avoids eagerly initializing unused finite enumerations in the arithmetic dependencies.
-/

/-- Compare both Rust captures and exercise the malformed-data and message-mutation checks. -/
def main : IO Unit := Zcash.Snark.Fixtures.Prover.checkCaptures
