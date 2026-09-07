import Zcash.Snark.ZeroKnowledge.PlonkPermutationMasking
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# The captured copy arguments use unrotated advice

Both public key layouts pass the finite query check used by the masking theorem.
This certifies the query syntax only; it does not establish sigma coherence, witness
validity, or correspondence between the reference constructor and Rust.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The captured one-Action permutation argument reads only unrotated advice queries. -/
theorem singleAction_plonkCopyQueries :
    plonkPermutationQueriesUnrotated Fixture.vk.permutationChunks = true := by
  decide +kernel

/-- The captured two-Action permutation argument reads only unrotated advice queries. -/
theorem multiAction_plonkCopyQueries :
    plonkPermutationQueriesUnrotated Fixture2.vk.permutationChunks = true := by
  decide +kernel

end Zcash.Snark.ZeroKnowledge
