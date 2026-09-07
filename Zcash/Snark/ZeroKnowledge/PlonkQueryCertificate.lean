import Zcash.Snark.ZeroKnowledge.PlonkQueryLayout
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# Captured verifier query-layout certificates

The two captured keys have the instance, advice, and fixed query orders used by
the reference proof constructor, including the final permutation rotation.
These finite checks identify query syntax, not the keys' commitment values.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The one-Action captured key satisfies every query-layout premise of the grouping connector. -/
theorem singleAction_plonkQueryLayout : PlonkQueryLayout (actions := 1) (k := 11) Fixture.vk := by
  constructor <;> decide +kernel

/-- The two-Action captured key has the same certified query ordering and blinding-row convention. -/
theorem multiAction_plonkQueryLayout : PlonkQueryLayout (actions := 2) (k := 11) Fixture2.vk := by
  constructor <;> decide +kernel

end Zcash.Snark.ZeroKnowledge
