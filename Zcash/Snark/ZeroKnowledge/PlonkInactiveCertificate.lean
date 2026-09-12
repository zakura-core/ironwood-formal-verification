import Zcash.Snark.ZeroKnowledge.PlonkInactiveRows
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# Captured Action expressions ignore advice when selectors are inactive

The kernel checks all gate expressions and both sides of every lookup with every
advice query marked changeable. Only zero packed selectors are supplied; values in
the fourteen original fixed columns are unknown. This is a property of the actual
captured expression lists, independent of any witness values.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- One-Action gate and lookup expressions are advice-independent when packed selectors are zero. -/
theorem singleAction_plonkInactiveExpressions :
    plonkInactiveExpressionsCheck (actions := 1) (k := 11) Fixture.vk = true := by
  decide +kernel

/-- The two-Action captured key has the same advice independence on inactive rows. -/
theorem multiAction_plonkInactiveExpressions :
    plonkInactiveExpressionsCheck (actions := 2) (k := 11) Fixture2.vk = true := by
  decide +kernel

end Zcash.Snark.ZeroKnowledge
