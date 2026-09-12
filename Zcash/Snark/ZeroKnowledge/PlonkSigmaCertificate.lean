import Zcash.Snark.ZeroKnowledge.PlonkKeygenSigma
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# Captured sigma-query indices and naming constants

The finite checks identify the sigma column of every packed entry and the delta
and chunk-stride constants used by both captured keys. Compiler sigma coherence can
therefore use these facts directly. These checks do not identify the full captured
key or its commitments with a compiled Action key.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (deltaFp)

/-- Every one-Action packed entry uses its global permutation-column sigma index. -/
theorem singleAction_plonkCopySigmaIndices : plonkCopySigmaIndices Fixture.vk.permutationChunks := by
  unfold plonkCopySigmaIndices
  decide +kernel

/-- The two-Action key uses the same packed sigma indices. -/
theorem multiAction_plonkCopySigmaIndices : plonkCopySigmaIndices Fixture2.vk.permutationChunks := by
  unfold plonkCopySigmaIndices
  decide +kernel

/-- The one-Action key uses the compiler's delta and the pinned seven-column stride. -/
theorem singleAction_plonkSigmaNaming : Fixture.vk.delta = deltaFp ∧ Fixture.vk.chunkLen = 7 := by
  decide +kernel

/-- The two-Action key uses the same compiler naming constants. -/
theorem multiAction_plonkSigmaNaming : Fixture2.vk.delta = deltaFp ∧ Fixture2.vk.chunkLen = 7 := by
  decide +kernel

end Zcash.Snark.ZeroKnowledge
