import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.SingleAction.Random.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Random.Fixture

/-!
# The captured blinding generator is nonidentity

All four checked-in captures place the same affine point at URS index 2048.
The coordinate lookups and curve equation below are checked by the kernel.
These proofs do not use the captures' native certificates for the full point list.
They establish nonidentity; the separate Vesta group-order argument supplies the
blinding bijection.
-/

namespace Zcash.Snark.ZeroKnowledge.CapturedBlinding

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta

private def wCoordinates : Fixture.Fq × Fixture.Fq :=
  (Fixture.mkFq 1717098781169229941 9391284368773822048 17460343927465935640 3151557595536469694,
   Fixture.mkFq 12634180106801823127 17616494652077801376 10681407423848128824 588705027306512953)

/-- The captured blinding coordinates lie on Vesta, allowing them to be interpreted as a valid group
point. -/
private theorem coordinates_onCurve : OnCurve Vesta.a Vesta.b wCoordinates := by
  decide +kernel

/-- The captured blinding point is nonidentity, discharging the simulator's hiding-generator
premise. -/
private theorem point_ne_zero : Fixture.mkVestaPoint wCoordinates ≠ 0 := by
  simp only [Fixture.mkVestaPoint, coordinates_onCurve, ↓reduceDIte]
  intro hzero
  have hx := congrArg SWPoint.x hzero
  change wCoordinates.1 = (0 : Fixture.Fq) at hx
  exact (by decide +kernel : wCoordinates.1 ≠ (0 : Fixture.Fq)) hx

/-- The captured nonidentity point remains at generator position 2,048 after decoding, connecting
coordinate data to the blinding premise. -/
private theorem pointFromCoordinates_ne_zero (coordinates : List (Fixture.Fq × Fixture.Fq))
    (pointOf : Fixture.Fq × Fixture.Fq → Fixture.G)
    (hcoordinates : coordinates[2048]? = some wCoordinates)
    (hpoint : pointOf wCoordinates ≠ 0) :
    (coordinates.map pointOf).getD 2048 0 ≠ 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcoordinates]
  exact hpoint

/-- The one-Action honest capture has a nonidentity URS blinding point. -/
theorem singleActionHonest_w_ne_zero : Fixture.capturedURS.w ≠ 0 := by
  dsimp only [Fixture.capturedURS, Fixture.capturedPoint, Fixture.capturedPoints]
  exact pointFromCoordinates_ne_zero _ _ (by decide +kernel) point_ne_zero

/-- The one-Action random capture has a nonidentity URS blinding point. -/
theorem singleActionRandom_w_ne_zero : FixtureRandom.capturedURS.w ≠ 0 := by
  dsimp only [FixtureRandom.capturedURS, FixtureRandom.capturedPoint, FixtureRandom.capturedPoints]
  exact pointFromCoordinates_ne_zero _ _ (by decide +kernel) point_ne_zero

/-- The two-Action honest capture has a nonidentity URS blinding point. -/
theorem multiActionHonest_w_ne_zero : Fixture2.capturedURS.w ≠ 0 := by
  dsimp only [Fixture2.capturedURS, Fixture2.capturedPoint, Fixture2.capturedPoints]
  exact pointFromCoordinates_ne_zero _ _ (by decide +kernel) point_ne_zero

/-- The two-Action random capture has a nonidentity URS blinding point. -/
theorem multiActionRandom_w_ne_zero : FixtureRandom2.capturedURS.w ≠ 0 := by
  dsimp only [FixtureRandom2.capturedURS, FixtureRandom2.capturedPoint, FixtureRandom2.capturedPoints]
  exact pointFromCoordinates_ne_zero _ _ (by decide +kernel) point_ne_zero

end Zcash.Snark.ZeroKnowledge.CapturedBlinding
