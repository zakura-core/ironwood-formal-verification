import Zcash.Circuits.Action.Planner

/-!
# The exact ordered Action region shapes

The table contains the 57 distinct region shapes in the source summaries. Each
stage has a kernel-checked equality to its reduced synthesis program; the table
is a computation certificate, not an assumed capture. Selector columns and their
order are retained, along with both empty regions. Merkle repetitions stay compact.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner Zcash.Circuits.Action

private abbrev a (index : ℕ) : RegionColumn := .column .advice index
private abbrev f (index : ℕ) : RegionColumn := .column .fixed index
private abbrev s (index : ℕ) : RegionColumn := .selector index
private abbrev shape (columns : List RegionColumn) (rows : ℕ) : RegionShapeSummary :=
  { columns := columns, rowCount := rows }

/-- The distinct source shapes; `a`, `f`, and `s` denote advice, fixed, and selector columns. -/
def actionRegionShapeTable : Array RegionShapeSummary :=
  #[shape [a 0] 1,
    shape [s 5, a 0, a 1] 1,
    shape [s 6, a 0, a 1] 1,
    shape [s 27, a 0, a 1, a 4, a 2, a 3] 1,
    shape [a 6] 1,
    shape [a 9, s 2, s 4] 3,
    shape [s 26, f 3, a 0, a 2, a 1, a 3, a 4, f 12, s 25] 53,
    shape [s 28, a 4, a 0, a 1, a 2, a 3] 2,
    shape [s 31, a 5, a 6, a 9, a 7, a 8] 1,
    shape [a 7] 1,
    shape [s 30, f 4, a 5, a 7, a 6, a 8, a 9, f 13, s 29] 53,
    shape [s 32, a 9, a 5, a 6, a 7, a 8] 2,
    shape [a 9] 1,
    shape [a 4, s 18, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, a 0, a 1, a 5, s 7, a 2, a 3] 23,
    shape [s 8, a 0, a 1, a 2, a 3, a 5, a 6, a 7, a 8, a 4, s 20] 2,
    shape [s 19, a 4, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, a 0, a 1, a 5, s 7, a 2, a 3] 85,
    shape [s 8, a 0, a 1, a 2, a 3, a 5, a 6, a 7, a 8, a 4] 2,
    shape [a 6, a 7, a 8] 1,
    shape [s 24, a 6, a 7, a 8] 3,
    shape [a 6, a 7, a 8, s 22, f 5, f 6, f 7, s 23, a 5, f 8, f 9, f 10] 37,
    shape [s 1, a 7, a 8, a 6] 1,
    shape [a 4, s 18, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, a 0, a 1, a 5, s 7, a 2, a 3] 86,
    shape [a 9, s 2, s 3] 14,
    shape [s 21, a 6, a 8, a 7] 3,
    shape [s 26, f 3, a 0, a 2, a 1, a 3, a 4, f 12, s 25] 52,
    shape [a 9, s 2, s 3] 15,
    shape [s 33, a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8] 2,
    shape [s 8, a 0, a 1, a 2, a 3, a 5, a 6, a 7, a 8, a 4, a 9, s 9, s 10, s 11, s 12, s 13, s 14, s 15, s 17] 137,
    shape [a 6, a 7, a 8, s 16] 3,
    shape [] 0,
    shape [a 9, s 2, s 3] 26,
    shape [s 44, a 5, a 6, a 7, a 8, a 9] 2,
    shape [s 26, f 3, a 0, a 2, a 1, a 3, a 4, f 12, s 25] 110,
    shape [s 34, a 6, a 7, a 8] 2,
    shape [s 35, a 6, a 7, a 8] 2,
    shape [s 36, a 6, a 7, a 8] 1,
    shape [s 37, a 6, a 7] 2,
    shape [s 38, a 6, a 7, a 8] 1,
    shape [a 6, a 7, a 8, a 9, s 39] 2,
    shape [a 6, a 7, a 8, a 9, s 40] 2,
    shape [s 41, a 6, a 7, a 8, a 9] 1,
    shape [a 6, a 7, a 8, a 9, s 42] 2,
    shape [a 6, a 7, a 8, a 9, s 43] 2,
    shape [s 55, a 5, a 6, a 7, a 8, a 9] 2,
    shape [s 30, f 4, a 5, a 7, a 6, a 8, a 9, f 13, s 29] 110,
    shape [s 45, a 6, a 7, a 8] 2,
    shape [s 46, a 6, a 7, a 8] 2,
    shape [s 47, a 6, a 7, a 8] 1,
    shape [s 48, a 6, a 7] 2,
    shape [s 49, a 6, a 7, a 8] 1,
    shape [a 6, a 7, a 8, a 9, s 50] 2,
    shape [a 6, a 7, a 8, a 9, s 51] 2,
    shape [s 52, a 6, a 7, a 8, a 9] 1,
    shape [a 6, a 7, a 8, a 9, s 53] 2,
    shape [a 6, a 7, a 8, a 9, s 54] 2,
    shape [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, s 0] 1,
    shape [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, s 0] 4]

private def shapesFrom (indices : List Nat) : List RegionShapeSummary :=
  indices.map (fun index => actionRegionShapeTable.getD index { columns := [], rowCount := 0 })

/-- The exact ordered witness-loading region shapes. -/
def actionWitnessRegionShapes : List RegionShapeSummary := shapesFrom [0, 0, 1, 2, 2, 0, 0, 0]

/-- The witness-loading source program computes the certified shapes. -/
theorem actionWitnessRegionShapes_eq_source :
    (Circuit.synthWitnessSynthesisSummary actionConfig).regionShapes = actionWitnessRegionShapes := by
  decide +kernel

/-- The exact ordered integrity-check region shapes. -/
def actionChecksRegionShapes : List RegionShapeSummary :=
  shapesFrom ((List.replicate 16 [3, 4, 5, 5, 4, 4, 6, 7]).flatten ++
    (List.replicate 16 [8, 9, 5, 5, 9, 9, 10, 11]).flatten ++
    [12, 12, 13, 14, 15, 16, 16, 17, 18, 19, 20, 21, 16, 22, 23, 16, 15, 16, 16, 4, 5, 5, 4, 4, 5, 4, 15, 16, 24, 16, 22, 25, 26, 27, 4, 22, 28, 2, 29])

/-- The integrity-check source program computes the certified shapes. -/
theorem actionChecksRegionShapes_eq_source :
    (Circuit.synthChecksSynthesisSummary actionConfig).regionShapes = actionChecksRegionShapes := by
  decide +kernel

/-- The exact ordered note-commitment region shapes. -/
def actionNotesRegionShapes : List RegionShapeSummary :=
  shapesFrom [4, 5, 5, 4, 4, 5, 4, 5, 5, 4, 4, 5, 4, 5, 4, 5, 5, 30, 22, 31,
    5, 5, 30, 22, 31, 15, 16, 32, 16, 22, 25, 25, 22, 33, 34, 35, 36, 37, 38, 39,
    40, 41, 42, 29, 2, 2, 0, 9, 5, 5, 9, 9, 5, 9, 5, 5, 9, 9, 5, 9,
    5, 9, 5, 5, 30, 22, 43, 5, 5, 30, 22, 43, 15, 16, 44, 16, 22, 25, 25, 22,
    45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

/-- The note-commitment source program computes the certified shapes. -/
theorem actionNotesRegionShapes_eq_source :
    (Circuit.synthNotesSynthesisSummary actionConfig).regionShapes = actionNotesRegionShapes := by
  decide +kernel

/-- The exact ordered cross-address region shapes. -/
def actionCrossAddressRegionShapes : List RegionShapeSummary := shapesFrom [56]

/-- The cross-address source program computes the certified shapes. -/
theorem actionCrossAddressRegionShapes_eq_source :
    (Circuit.synthCrossAddressChecksSynthesisSummary actionConfig).regionShapes = actionCrossAddressRegionShapes := by
  decide +kernel

/-- The complete ordered 395-region input to Action's V1 planner. -/
def actionOrderedRegionShapes : List RegionShapeSummary :=
  actionWitnessRegionShapes ++ actionChecksRegionShapes ++ actionNotesRegionShapes ++
    actionCrossAddressRegionShapes

/-- The compositional source summary is exactly the certified ordered planner input. -/
theorem actionOrderedRegionShapes_eq_source :
    (Circuit.mainPostSynthesisSummary actionConfig).regionShapes = actionOrderedRegionShapes := by
  simp only [Circuit.mainPostSynthesisSummary, Circuit.synthesizeBaseSynthesisSummary,
    SynthesisSummary.combine_regionShapes, actionWitnessRegionShapes_eq_source,
    actionChecksRegionShapes_eq_source, actionNotesRegionShapes_eq_source,
    actionCrossAddressRegionShapes_eq_source, actionOrderedRegionShapes, List.append_assoc]

/-- The certified planner input retains all 395 source regions, including empty ones. -/
theorem actionOrderedRegionShapes_length : actionOrderedRegionShapes.length = 395 := by
  decide +kernel

/-- Every certified shape has distinct columns and a positive height whenever it uses columns. -/
theorem actionOrderedRegionShapes_wellFormed :
    actionOrderedRegionShapes.Forall RegionShapeSummary.WellFormed := by
  unfold RegionShapeSummary.WellFormed
  decide +kernel

end Zcash.Snark.ZeroKnowledge
