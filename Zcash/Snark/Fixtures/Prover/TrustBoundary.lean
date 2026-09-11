import Zcash.Snark.Fixtures.Prover.Replay
import Zcash.Meta.AxiomCheck

/-!
# Trust boundary of the prover execution check

The replay equality holds for every decoded input and uses no captured outputs.
These pins check its dependency axioms and the computability of its input decoder
and execution path. Lean CI separately executes `Main.lean` for the concrete
comparisons; those evaluations do not add theorem axioms.
The group equalities inherit the existing Vesta order certificate.
-/

assert_axioms Zcash.Snark.Fixtures.Prover.interpolateRows_result
assert_axioms Zcash.Snark.Fixtures.Prover.multiply_result
assert_axioms Zcash.Snark.Fixtures.Prover.material_result
assert_axioms Zcash.Snark.Fixtures.Prover.numerator_result
assert_axioms Zcash.Snark.Fixtures.Prover.quotientPieces_result
assert_axioms Zcash.Snark.Fixtures.Prover.ipaFromTape_result +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixtures.Prover.proofFromRows_result +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixtures.Prover.execute_result +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.Fixtures.Prover.replay_eq_reference_capstone +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)

assert_computable Zcash.Snark.Fixtures.Prover.decodeCapture +choice
assert_computable Zcash.Snark.Fixtures.Prover.execute +choice
assert_computable Zcash.Snark.Fixtures.Prover.replayProof +choice
