import Zcash.Snark.ZeroKnowledge.PlonkMaskBoundary
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture

/-!
# Kernel certificates for the captured keys' mask boundaries

The fixed-query values below were read from `Zcash/Circuits/Fixtures/actionLayout.json`
(SHA-256 `7ac082324c93ef6c097ad26dfe7a166d1a74e41a5a6b4c0e250bf3e3d2163a87`),
using the pinned fixed-query order. Row 0 has nonzero query entries 0, 11, 12, and 19;
row 2041 retains the two generator-table entries 11 and 12; rows 2042 through 2047
have no fixed assignments. The checks use the actual captured verifier-key expressions.

These certificates prove mask safety for the stated public row values. Equality of
the supplied public polynomials with these values remains an explicit premise; this
file does not prove Rust keygen correspondence or authenticate the JSON capture.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Captured fixed-query values on row 0 and rows 2041 through 2047, with zero fallback. -/
def capturedPlonkMaskBoundaryFixed (row : Fin 8) (query : ℕ) : Fp :=
  if row.val = 0 then
    match query with
    | 0 => 28043396612162516079146097931791602683257960966880886943581093115464031141889
    | 11 => 6200097879647205583499851243213148560621730003917924543823561700220554504799
    | 12 => 21285653556795296467031706491948305595095309413618206259690549906869937136771
    | 19 => 4
    | _ => 0
  else if row.val = 1 then
    match query with
    | 11 => 6200097879647205583499851243213148560621730003917924543823561700220554504799
    | 12 => 21285653556795296467031706491948305595095309413618206259690549906869937136771
    | _ => 0
  else 0

/-- The captured one-Action gate and lookup expressions pass all boundary mask checks. -/
theorem singleAction_plonkMaskBoundary :
    plonkMaskBoundaryCheck (actions := 1) (k := 11) Fixture.vk capturedPlonkMaskBoundaryFixed = true := by
  decide +kernel

/-- The captured two-Action gate and lookup expressions pass the same public boundary checks. -/
theorem multiAction_plonkMaskBoundary :
    plonkMaskBoundaryCheck (actions := 2) (k := 11) Fixture2.vk capturedPlonkMaskBoundaryFixed = true := by
  decide +kernel

/-- Matching the stated public boundary rows instantiates the one-Action mask profile. -/
theorem singleAction_plonkMaskingProfile (pub : PlonkPublicPolynomials 1)
    (hfixed : ∀ row, plonkFixedRowValues pub (plonkMaskBoundaryRows row) = capturedPlonkMaskBoundaryFixed row) :
    PlonkMaskingProfile (k := 11) Fixture.vk pub :=
  plonkMaskBoundaryCheck_sound (k := 11) Fixture.vk pub capturedPlonkMaskBoundaryFixed hfixed
    singleAction_plonkMaskBoundary

/-- Matching the stated public boundary rows instantiates the two-Action mask profile. -/
theorem multiAction_plonkMaskingProfile (pub : PlonkPublicPolynomials 2)
    (hfixed : ∀ row, plonkFixedRowValues pub (plonkMaskBoundaryRows row) = capturedPlonkMaskBoundaryFixed row) :
    PlonkMaskingProfile (k := 11) Fixture2.vk pub :=
  plonkMaskBoundaryCheck_sound (k := 11) Fixture2.vk pub capturedPlonkMaskBoundaryFixed hfixed
    multiAction_plonkMaskBoundary

end Zcash.Snark.ZeroKnowledge
