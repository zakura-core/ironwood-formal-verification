import Zcash.Snark.ZeroKnowledge.PlonkPartialMaskBoundary
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# Captured expressions need only the packed selector boundary values

The certificates leave every query into the fourteen original fixed columns unknown.
Consequently no table element, generator coordinate, or region-fixed constant is
needed for these mask checks. Row 0 needs only zero in columns 18, 20, 21, and 24;
the other selector values there are unrestricted. All fifteen packed selectors are
zero at the later boundaries. These values still have to follow from the public
columns generated for the circuit.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- The one-Action expressions pass with only the stated packed-selector boundary values. -/
theorem singleAction_plonkSelectorBoundary :
    plonkPartialMaskBoundaryCheck (actions := 1) (k := 11) Fixture.vk plonkSelectorBoundaryKnown = true := by
  decide +kernel

/-- The two-Action expressions pass with the same selector information and arbitrary other fixed values. -/
theorem multiAction_plonkSelectorBoundary :
    plonkPartialMaskBoundaryCheck (actions := 2) (k := 11) Fixture2.vk plonkSelectorBoundaryKnown = true := by
  decide +kernel

end Zcash.Snark.ZeroKnowledge
