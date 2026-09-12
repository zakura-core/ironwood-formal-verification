import Zcash.Snark.ZeroKnowledge.PlonkPermutationMasking
import Zcash.Snark.ZeroKnowledge.PlonkKeygenCopies
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# Captured copy-query and chunk-width certificates

Both public key layouts pass the finite query check used by the masking theorem and
have the seven/seven/one chunk widths used to pack compiler copies. These certify
query syntax and widths; they do not establish sigma coherence, witness
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

/-- The captured one-Action key packs its fifteen permutation columns into widths seven, seven, and one. -/
theorem singleAction_plonkCopyChunkWidths : plonkCopyChunkWidths Fixture.vk.permutationChunks := by
  unfold plonkCopyChunkWidths
  decide +kernel

/-- The two-Action captured key has the same permutation chunk widths. -/
theorem multiAction_plonkCopyChunkWidths : plonkCopyChunkWidths Fixture2.vk.permutationChunks := by
  unfold plonkCopyChunkWidths
  decide +kernel

end Zcash.Snark.ZeroKnowledge
