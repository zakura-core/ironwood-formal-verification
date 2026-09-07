import Zcash.Snark.ZeroKnowledge.VestaSimulation
import Zcash.Snark.ZeroKnowledge.CapturedBlinding
import Zcash.Meta.AxiomCheck

/-!
# The concrete Vesta boundary of the zero-knowledge development

The general simulation, canonical codecs, and tape/observation connection are
pinned at the standard tier in the parent census. Concrete scalar blinding uses
Vesta's existing group-cardinality and scalar-module construction, whose native
dependency is named below. This file introduces no new native certificate.

The four captured nonidentity checks use kernel reduction of the coordinates and
curve equation. They do not depend on the fixtures' native whole-list checks or
on the Vesta point-order certificate.
-/

assert_axioms Zcash.Snark.ZeroKnowledge.CapturedBlinding.singleActionHonest_w_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.CapturedBlinding.singleActionRandom_w_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.CapturedBlinding.multiActionHonest_w_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.CapturedBlinding.multiActionRandom_w_ne_zero

assert_axioms Zcash.Snark.ZeroKnowledge.vestaBlinding_bijective +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.vestaBlinding_bijective_iff +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideVestaPlonkReferenceAttempt_failure_le +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideVestaCompilerKeygenPlonk_simulation_error_bound +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideVestaSuccessfulCompilerKeygenPlonk_simulation_capstone +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
assert_axioms Zcash.Snark.ZeroKnowledge.wideVestaRetriedCompilerKeygenPlonk_simulation_capstone +native(
  CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt)
