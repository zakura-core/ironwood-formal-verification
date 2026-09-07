import Zcash.Snark.ZeroKnowledge.ActionSimulation
import Zcash.Meta.AxiomCheck

/-!
# The actual Action circuit boundary of the zero-knowledge development

The general selector-padding argument remains in the standard-tier parent census.
Action's public-input layout and compiler data are reached through the existing
opaque circuit package and its proved API. That package carries the named Pallas
point-order dependency. The encoded Vesta comparison additionally carries the
existing Vesta point-order dependency. No new native certificate is introduced.

The four initial selector zeros remain an explicit proposition, not a certificate.
The key-expression checks use the already kernel-checked captured-key predicates.
-/

assert_axioms Zcash.Snark.ZeroKnowledge.ActionInitialSelectorsZero +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionInstanceRows +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionInstanceRows_eq_elements +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_computable Zcash.Snark.ZeroKnowledge.actionPublicPolynomials +choice +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicPolynomials_instances_eval +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.action_plonkSelectorMaskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.actionPublicPolynomials_maskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.singleAction_actionPublicPolynomials_maskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.multiAction_actionPublicPolynomials_maskingProfile +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideActionReference_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
