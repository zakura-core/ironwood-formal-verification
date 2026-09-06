import Zcash.Snark.ZeroKnowledge.PlonkDegree
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# Kernel-checked degree profiles of the captured keys

Only the public expression syntax and permutation-chunk lengths are inspected here.
These certificates use kernel reduction, and do not depend on the earlier native
degree checks or establish a Rust-to-Lean correspondence.
-/

namespace Zcash.Snark.ZeroKnowledge

set_option maxRecDepth 10000 in
/-- The one-Action captured key fits the eight-piece quotient profile. -/
theorem singleAction_plonkDegreeProfile :
    PlonkDegreeProfile (actions := 1) (k := 11) Fixture.vk := by
  constructor <;> decide +kernel

set_option maxRecDepth 10000 in
/-- The two-Action captured key has the same sufficient public degree profile. -/
theorem multiAction_plonkDegreeProfile :
    PlonkDegreeProfile (actions := 2) (k := 11) Fixture2.vk := by
  constructor <;> decide +kernel

end Zcash.Snark.ZeroKnowledge
