import Zcash.Snark.ZeroKnowledge.Zakura.Action
import Zcash.Snark.ZeroKnowledge.Zakura.Completeness
import Zcash.Snark.ZeroKnowledge.Zakura.Regression
import Zcash.Snark.ZeroKnowledge.Zakura.MultiopenRegression

/-!
# Trust census for the Zakura release observation

The API observation adds no native proof computation. The Action instantiation
inherits the same two Pasta group-order origins as the reference simulation.
The runtime correspondence and release provenance are documented separately.
-/

assert_computable Zcash.Snark.ZeroKnowledge.Zakura.observeAttempt
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.observeAttempt_complete
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.observeAttempt_duplicate
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.observeAttempt_zeroIpa
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.observeAttempt_earlyIdentity
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.observeAttempt_openingIdentity
assert_computable Zcash.Snark.ZeroKnowledge.Zakura.acceptsPublicPrefix +choice
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.acceptsPublicPrefix_iff
assert_computable Zcash.Snark.ZeroKnowledge.Zakura.observeOracleResult
assert_computable Zcash.Snark.ZeroKnowledge.Zakura.actionRunTape +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionProver +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionSimulator +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionRunTape_law +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionRunTape_rejects +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.action_publicRejection +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.action_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.completedCall_returnsBytes
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.adviceIdentity_returnsError
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.duplicateQueries_returnError
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.quotientIdentity_returnsError
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.firstZeroIpa_panics
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.duplicateQueries_stopBeforeQuotient
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.rightIdentity_precedesZeroChallenge
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.publicIdentity_rejected
assert_computable Zcash.Snark.ZeroKnowledge.Zakura.linearCollisionGroup
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.linearCollisionGroup_quotient
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.openingNodeCollision_usesPolynomialValue

-- Acceptance of initialized calls with a fresh random oracle.
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionRunTape_empty_eq_programmed +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionAcceptedCallSet +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionAcceptedCallSet_returns_proof +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionRunTape_mem_acceptedCallSet +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.action_completeness_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionWitness_completeness_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionWitness_acceptance_probability_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.actionWitness_completeness_binary_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.Zakura.action_initialization_failure +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
