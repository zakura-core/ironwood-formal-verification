import Zcash.Snark.Fixtures.Prover.Check

/-!
# Running the captured prover executions

`lake env lean --run Zcash/Snark/Fixtures/Prover/Main.lean` runs the checks after
the default build, including when build artifacts are cached. The interpreter
avoids eagerly initializing unused finite enumerations in the arithmetic dependencies.

The optional `single` and `multi` arguments select one complete capture. CI runs
these independent cases concurrently and requires both processes to succeed.
-/

/-- Compare both Rust captures and exercise the malformed-data and message-mutation checks. -/
def main (args : List String) : IO Unit :=
  match args with
  | [] => Zcash.Snark.Fixtures.Prover.checkCaptures
  | ["single"] => Zcash.Snark.Fixtures.Prover.checkSingleCapture
  | ["multi"] => Zcash.Snark.Fixtures.Prover.checkMultiCapture
  | _ => throw (IO.userError "usage: Main.lean [single|multi]")
