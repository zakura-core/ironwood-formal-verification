import Zcash.Snark.ZeroKnowledge.PlonkProductBounds
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# Kernel-checked product dimensions of the captured keys

Both public keys have the three chunks used by the computed constraint theorem and
the fifteen packed references used by the numerical denominator bound. These finite
syntax checks do not establish correspondence between the reference prover and Rust.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The captured one-Action key has three chunks and fifteen packed permutation references. -/
theorem singleAction_plonkProductShape :
    Fixture.vk.permutationChunks.length = 3 ∧ Fixture.vk.permutationChunks.flatten.length = 15 := by
  constructor <;> decide +kernel

/-- The captured two-Action key has the same packed permutation dimensions. -/
theorem multiAction_plonkProductShape :
    Fixture2.vk.permutationChunks.length = 3 ∧ Fixture2.vk.permutationChunks.flatten.length = 15 := by
  constructor <;> decide +kernel

end Zcash.Snark.ZeroKnowledge
