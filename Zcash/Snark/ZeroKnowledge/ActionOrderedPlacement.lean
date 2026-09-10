import Zcash.Snark.ZeroKnowledge.ActionOrderedShapes
import Zcash.Snark.ZeroKnowledge.PlannerStarts

/-!
# Exact start rows for Action's ordered placement certificate

Each block certifies its least fitting start and the free run occupied by its
repeated regions. All columns, including selectors, are retained. The two empty
regions follow the trace with zero starts. `ActionOrderedSort` certifies the exact
legacy-sort order, and `ActionOrderedStarts` connects these starts to the compiler's
complete plan in original region order.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner Halo2.FloorPlanner.V1

private abbrev shape0 : RegionShapeSummary := { columns := [.column .advice 0], rowCount := 1 }
private abbrev shape1 : RegionShapeSummary := { columns := [.selector 5, .column .advice 0, .column .advice 1], rowCount := 1 }
private abbrev shape2 : RegionShapeSummary := { columns := [.selector 6, .column .advice 0, .column .advice 1], rowCount := 1 }
private abbrev shape3 : RegionShapeSummary := { columns := [.selector 27, .column .advice 0, .column .advice 1, .column .advice 4, .column .advice 2, .column .advice 3], rowCount := 1 }
private abbrev shape4 : RegionShapeSummary := { columns := [.column .advice 6], rowCount := 1 }
private abbrev shape5 : RegionShapeSummary := { columns := [.column .advice 9, .selector 2, .selector 4], rowCount := 3 }
private abbrev shape6 : RegionShapeSummary := { columns := [.selector 26, .column .fixed 3, .column .advice 0, .column .advice 2, .column .advice 1, .column .advice 3, .column .advice 4, .column .fixed 12, .selector 25], rowCount := 53 }
private abbrev shape7 : RegionShapeSummary := { columns := [.selector 28, .column .advice 4, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3], rowCount := 2 }
private abbrev shape8 : RegionShapeSummary := { columns := [.selector 31, .column .advice 5, .column .advice 6, .column .advice 9, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev shape9 : RegionShapeSummary := { columns := [.column .advice 7], rowCount := 1 }
private abbrev shape10 : RegionShapeSummary := { columns := [.selector 30, .column .fixed 4, .column .advice 5, .column .advice 7, .column .advice 6, .column .advice 8, .column .advice 9, .column .fixed 13, .selector 29], rowCount := 53 }
private abbrev shape11 : RegionShapeSummary := { columns := [.selector 32, .column .advice 9, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev shape12 : RegionShapeSummary := { columns := [.column .advice 9], rowCount := 1 }
private abbrev shape13 : RegionShapeSummary := { columns := [.column .advice 4, .selector 18, .column .fixed 3, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 9, .column .fixed 10, .column .fixed 11, .column .advice 0, .column .advice 1, .column .advice 5, .selector 7, .column .advice 2, .column .advice 3], rowCount := 23 }
private abbrev shape14 : RegionShapeSummary := { columns := [.selector 8, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 4, .selector 20], rowCount := 2 }
private abbrev shape15 : RegionShapeSummary := { columns := [.selector 19, .column .advice 4, .column .fixed 3, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 9, .column .fixed 10, .column .fixed 11, .column .advice 0, .column .advice 1, .column .advice 5, .selector 7, .column .advice 2, .column .advice 3], rowCount := 85 }
private abbrev shape16 : RegionShapeSummary := { columns := [.selector 8, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 4], rowCount := 2 }
private abbrev shape17 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev shape18 : RegionShapeSummary := { columns := [.selector 24, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 3 }
private abbrev shape19 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .selector 22, .column .fixed 5, .column .fixed 6, .column .fixed 7, .selector 23, .column .advice 5, .column .fixed 8, .column .fixed 9, .column .fixed 10], rowCount := 37 }
private abbrev shape20 : RegionShapeSummary := { columns := [.selector 1, .column .advice 7, .column .advice 8, .column .advice 6], rowCount := 1 }
private abbrev shape21 : RegionShapeSummary := { columns := [.column .advice 4, .selector 18, .column .fixed 3, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 9, .column .fixed 10, .column .fixed 11, .column .advice 0, .column .advice 1, .column .advice 5, .selector 7, .column .advice 2, .column .advice 3], rowCount := 86 }
private abbrev shape22 : RegionShapeSummary := { columns := [.column .advice 9, .selector 2, .selector 3], rowCount := 14 }
private abbrev shape23 : RegionShapeSummary := { columns := [.selector 21, .column .advice 6, .column .advice 8, .column .advice 7], rowCount := 3 }
private abbrev shape24 : RegionShapeSummary := { columns := [.selector 26, .column .fixed 3, .column .advice 0, .column .advice 2, .column .advice 1, .column .advice 3, .column .advice 4, .column .fixed 12, .selector 25], rowCount := 52 }
private abbrev shape25 : RegionShapeSummary := { columns := [.column .advice 9, .selector 2, .selector 3], rowCount := 15 }
private abbrev shape26 : RegionShapeSummary := { columns := [.selector 33, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 4, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev shape27 : RegionShapeSummary := { columns := [.selector 8, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 4, .column .advice 9, .selector 9, .selector 10, .selector 11, .selector 12, .selector 13, .selector 14, .selector 15, .selector 17], rowCount := 137 }
private abbrev shape28 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .selector 16], rowCount := 3 }
private abbrev shape29 : RegionShapeSummary := { columns := [], rowCount := 0 }
private abbrev shape30 : RegionShapeSummary := { columns := [.column .advice 9, .selector 2, .selector 3], rowCount := 26 }
private abbrev shape31 : RegionShapeSummary := { columns := [.selector 44, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9], rowCount := 2 }
private abbrev shape32 : RegionShapeSummary := { columns := [.selector 26, .column .fixed 3, .column .advice 0, .column .advice 2, .column .advice 1, .column .advice 3, .column .advice 4, .column .fixed 12, .selector 25], rowCount := 110 }
private abbrev shape33 : RegionShapeSummary := { columns := [.selector 34, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev shape34 : RegionShapeSummary := { columns := [.selector 35, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev shape35 : RegionShapeSummary := { columns := [.selector 36, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev shape36 : RegionShapeSummary := { columns := [.selector 37, .column .advice 6, .column .advice 7], rowCount := 2 }
private abbrev shape37 : RegionShapeSummary := { columns := [.selector 38, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev shape38 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 39], rowCount := 2 }
private abbrev shape39 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 40], rowCount := 2 }
private abbrev shape40 : RegionShapeSummary := { columns := [.selector 41, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9], rowCount := 1 }
private abbrev shape41 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 42], rowCount := 2 }
private abbrev shape42 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 43], rowCount := 2 }
private abbrev shape43 : RegionShapeSummary := { columns := [.selector 55, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9], rowCount := 2 }
private abbrev shape44 : RegionShapeSummary := { columns := [.selector 30, .column .fixed 4, .column .advice 5, .column .advice 7, .column .advice 6, .column .advice 8, .column .advice 9, .column .fixed 13, .selector 29], rowCount := 110 }
private abbrev shape45 : RegionShapeSummary := { columns := [.selector 45, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev shape46 : RegionShapeSummary := { columns := [.selector 46, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev shape47 : RegionShapeSummary := { columns := [.selector 47, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev shape48 : RegionShapeSummary := { columns := [.selector 48, .column .advice 6, .column .advice 7], rowCount := 2 }
private abbrev shape49 : RegionShapeSummary := { columns := [.selector 49, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev shape50 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 50], rowCount := 2 }
private abbrev shape51 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 51], rowCount := 2 }
private abbrev shape52 : RegionShapeSummary := { columns := [.selector 52, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9], rowCount := 1 }
private abbrev shape53 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 53], rowCount := 2 }
private abbrev shape54 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 54], rowCount := 2 }
private abbrev shape55 : RegionShapeSummary := { columns := [.column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 4, .column .advice 5, .column .advice 6, .column .advice 7, .selector 0], rowCount := 1 }
private abbrev shape56 : RegionShapeSummary := { columns := [.column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 4, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 0], rowCount := 4 }

private abbrev block (count : ℕ) (summary : RegionShapeSummary) (start : ℕ) : PlannedSummaryBlock :=
  { count := count, summary := summary, start := start }

/-- The 181 consecutive placement blocks, in the candidate descending sort order. -/
def actionSortedPlacementTrace : List PlannedSummaryBlock :=
  [block 1 shape27 0,
    block 1 shape32 137,
    block 1 shape44 137,
    block 1 shape21 247,
    block 5 shape15 333,
    block 1 shape10 758,
    block 2 shape6 758,
    block 2 shape10 811,
    block 2 shape6 864,
    block 2 shape10 917,
    block 1 shape6 970,
    block 1 shape10 1023,
    block 2 shape6 1023,
    block 3 shape10 1076,
    block 1 shape6 1129,
    block 5 shape10 1235,
    block 1 shape6 1182,
    block 1 shape10 1500,
    block 5 shape6 1235,
    block 1 shape10 1553,
    block 2 shape6 1500,
    block 1 shape24 1606,
    block 1 shape19 1606,
    block 1 shape13 1658,
    block 1 shape56 1681,
    block 4 shape30 247,
    block 3 shape16 1685,
    block 1 shape14 1691,
    block 8 shape16 1693,
    block 1 shape26 1709,
    block 1 shape16 1711,
    block 5 shape25 351,
    block 11 shape22 426,
    block 1 shape7 1713,
    block 1 shape11 1643,
    block 1 shape31 1645,
    block 1 shape11 1647,
    block 1 shape43 1649,
    block 1 shape7 1715,
    block 1 shape11 1651,
    block 1 shape31 1653,
    block 2 shape7 1717,
    block 1 shape11 1655,
    block 3 shape11 1713,
    block 1 shape43 1719,
    block 1 shape7 1721,
    block 2 shape11 1721,
    block 1 shape7 1723,
    block 1 shape11 1725,
    block 1 shape7 1725,
    block 1 shape11 1727,
    block 1 shape7 1727,
    block 1 shape11 1729,
    block 1 shape7 1729,
    block 1 shape11 1731,
    block 2 shape7 1731,
    block 1 shape11 1733,
    block 2 shape7 1735,
    block 2 shape11 1735,
    block 3 shape7 1739,
    block 1 shape28 247,
    block 1 shape18 250,
    block 1 shape23 253,
    block 1 shape39 580,
    block 1 shape55 1745,
    block 1 shape42 582,
    block 1 shape54 584,
    block 1 shape38 586,
    block 1 shape53 588,
    block 1 shape51 590,
    block 1 shape50 592,
    block 1 shape41 594,
    block 1 shape33 256,
    block 1 shape45 258,
    block 1 shape34 260,
    block 1 shape46 262,
    block 1 shape3 1746,
    block 1 shape8 1657,
    block 1 shape3 1747,
    block 1 shape8 1739,
    block 1 shape3 1748,
    block 1 shape8 1740,
    block 1 shape3 1749,
    block 3 shape8 1741,
    block 3 shape3 1750,
    block 1 shape8 1744,
    block 1 shape8 1746,
    block 2 shape3 1753,
    block 1 shape8 1747,
    block 1 shape3 1755,
    block 1 shape8 1748,
    block 2 shape3 1756,
    block 2 shape8 1749,
    block 2 shape3 1758,
    block 1 shape8 1751,
    block 1 shape3 1760,
    block 2 shape8 1752,
    block 1 shape3 1761,
    block 1 shape8 1754,
    block 1 shape40 596,
    block 1 shape52 597,
    block 1 shape48 264,
    block 1 shape36 266,
    block 2 shape5 598,
    block 1 shape35 268,
    block 1 shape5 604,
    block 1 shape37 269,
    block 50 shape5 607,
    block 12 shape5 1606,
    block 2 shape5 1658,
    block 1 shape47 270,
    block 5 shape5 1664,
    block 2 shape5 1685,
    block 1 shape49 271,
    block 1 shape17 272,
    block 1 shape20 273,
    block 7 shape5 1691,
    block 8 shape5 1755,
    block 1 shape1 1762,
    block 5 shape2 1763,
    block 1 shape9 274,
    block 2 shape4 274,
    block 2 shape9 275,
    block 1 shape4 276,
    block 3 shape9 277,
    block 2 shape4 277,
    block 2 shape9 280,
    block 1 shape4 279,
    block 3 shape9 282,
    block 2 shape4 280,
    block 2 shape9 285,
    block 1 shape4 282,
    block 3 shape9 287,
    block 2 shape4 283,
    block 1 shape9 290,
    block 1 shape0 1768,
    block 1 shape4 285,
    block 3 shape9 291,
    block 2 shape4 286,
    block 2 shape9 294,
    block 1 shape4 288,
    block 3 shape9 296,
    block 2 shape4 289,
    block 2 shape9 299,
    block 1 shape4 291,
    block 3 shape9 301,
    block 2 shape4 292,
    block 2 shape9 304,
    block 1 shape4 294,
    block 3 shape9 306,
    block 1 shape4 295,
    block 1 shape0 1769,
    block 3 shape4 296,
    block 3 shape9 309,
    block 2 shape4 299,
    block 2 shape9 312,
    block 1 shape4 301,
    block 2 shape9 314,
    block 1 shape12 757,
    block 2 shape4 302,
    block 1 shape12 1642,
    block 8 shape4 304,
    block 2 shape9 316,
    block 13 shape4 312,
    block 1 shape0 1770,
    block 2 shape4 325,
    block 2 shape9 318,
    block 1 shape4 327,
    block 1 shape9 320,
    block 1 shape0 1771,
    block 2 shape4 328,
    block 2 shape9 321,
    block 1 shape4 330,
    block 3 shape9 323,
    block 2 shape4 331,
    block 2 shape9 326,
    block 1 shape4 333,
    block 1 shape9 328,
    block 2 shape0 1772,
    block 1 shape4 334,
    block 1 shape9 329]


section

-- The concrete prefix contains up to 181 blocks; keep the larger depth local.
set_option maxRecDepth 4096

/-- Placement blocks 0 through 2 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk0 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 0) ((actionSortedPlacementTrace.drop 0).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 3 through 5 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk3 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 3) ((actionSortedPlacementTrace.drop 3).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 6 through 8 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk6 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 6) ((actionSortedPlacementTrace.drop 6).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 9 through 11 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk9 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 9) ((actionSortedPlacementTrace.drop 9).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 12 through 14 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk12 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 12) ((actionSortedPlacementTrace.drop 12).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 15 through 17 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk15 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 15) ((actionSortedPlacementTrace.drop 15).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 18 through 20 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk18 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 18) ((actionSortedPlacementTrace.drop 18).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 21 through 23 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk21 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 21) ((actionSortedPlacementTrace.drop 21).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 24 through 26 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk24 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 24) ((actionSortedPlacementTrace.drop 24).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 27 through 29 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk27 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 27) ((actionSortedPlacementTrace.drop 27).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 30 through 32 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk30 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 30) ((actionSortedPlacementTrace.drop 30).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 33 through 35 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk33 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 33) ((actionSortedPlacementTrace.drop 33).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 36 through 38 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk36 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 36) ((actionSortedPlacementTrace.drop 36).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 39 through 41 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk39 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 39) ((actionSortedPlacementTrace.drop 39).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 42 through 44 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk42 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 42) ((actionSortedPlacementTrace.drop 42).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 45 through 47 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk45 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 45) ((actionSortedPlacementTrace.drop 45).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 48 through 50 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk48 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 48) ((actionSortedPlacementTrace.drop 48).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 51 through 53 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk51 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 51) ((actionSortedPlacementTrace.drop 51).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 54 through 56 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk54 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 54) ((actionSortedPlacementTrace.drop 54).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 57 through 59 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk57 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 57) ((actionSortedPlacementTrace.drop 57).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 60 through 62 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk60 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 60) ((actionSortedPlacementTrace.drop 60).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 63 through 65 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk63 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 63) ((actionSortedPlacementTrace.drop 63).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 66 through 68 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk66 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 66) ((actionSortedPlacementTrace.drop 66).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 69 through 71 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk69 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 69) ((actionSortedPlacementTrace.drop 69).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 72 through 74 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk72 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 72) ((actionSortedPlacementTrace.drop 72).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 75 through 77 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk75 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 75) ((actionSortedPlacementTrace.drop 75).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 78 through 80 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk78 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 78) ((actionSortedPlacementTrace.drop 78).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 81 through 83 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk81 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 81) ((actionSortedPlacementTrace.drop 81).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 84 through 86 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk84 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 84) ((actionSortedPlacementTrace.drop 84).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 87 through 89 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk87 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 87) ((actionSortedPlacementTrace.drop 87).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 90 through 92 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk90 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 90) ((actionSortedPlacementTrace.drop 90).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 93 through 95 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk93 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 93) ((actionSortedPlacementTrace.drop 93).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 96 through 98 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk96 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 96) ((actionSortedPlacementTrace.drop 96).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 99 through 101 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk99 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 99) ((actionSortedPlacementTrace.drop 99).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 102 through 104 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk102 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 102) ((actionSortedPlacementTrace.drop 102).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 105 through 107 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk105 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 105) ((actionSortedPlacementTrace.drop 105).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 108 through 110 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk108 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 108) ((actionSortedPlacementTrace.drop 108).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 111 through 113 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk111 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 111) ((actionSortedPlacementTrace.drop 111).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 114 through 116 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk114 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 114) ((actionSortedPlacementTrace.drop 114).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 117 through 119 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk117 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 117) ((actionSortedPlacementTrace.drop 117).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 120 through 122 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk120 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 120) ((actionSortedPlacementTrace.drop 120).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 123 through 125 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk123 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 123) ((actionSortedPlacementTrace.drop 123).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 126 through 128 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk126 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 126) ((actionSortedPlacementTrace.drop 126).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 129 through 131 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk129 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 129) ((actionSortedPlacementTrace.drop 129).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 132 through 134 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk132 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 132) ((actionSortedPlacementTrace.drop 132).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 135 through 137 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk135 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 135) ((actionSortedPlacementTrace.drop 135).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 138 through 140 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk138 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 138) ((actionSortedPlacementTrace.drop 138).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 141 through 143 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk141 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 141) ((actionSortedPlacementTrace.drop 141).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 144 through 146 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk144 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 144) ((actionSortedPlacementTrace.drop 144).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 147 through 149 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk147 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 147) ((actionSortedPlacementTrace.drop 147).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 150 through 152 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk150 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 150) ((actionSortedPlacementTrace.drop 150).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 153 through 155 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk153 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 153) ((actionSortedPlacementTrace.drop 153).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 156 through 158 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk156 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 156) ((actionSortedPlacementTrace.drop 156).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 159 through 161 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk159 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 159) ((actionSortedPlacementTrace.drop 159).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 162 through 164 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk162 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 162) ((actionSortedPlacementTrace.drop 162).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 165 through 167 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk165 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 165) ((actionSortedPlacementTrace.drop 165).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 168 through 170 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk168 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 168) ((actionSortedPlacementTrace.drop 168).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 171 through 173 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk171 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 171) ((actionSortedPlacementTrace.drop 171).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 174 through 176 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk174 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 174) ((actionSortedPlacementTrace.drop 174).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 177 through 179 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk177 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 177) ((actionSortedPlacementTrace.drop 177).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 3 planner_trace_step [block]
  trivial

/-- Placement blocks 180 through 180 fit lawfully after their preceding blocks. This supplies one
segment of the complete placement certificate. -/
private theorem traceChunk180 : PlannedSummaryBlock.TraceLawfulAfter
    (actionSortedPlacementTrace.take 180) ((actionSortedPlacementTrace.drop 180).take 3) := by
  unfold actionSortedPlacementTrace
  iterate 1 planner_trace_step [block]
  trivial

/-- Consecutive lawful three-block chunks certify their whole prefix, allowing the placement proof
to compose small certificates. -/
private theorem lawful_take_chunks (trace : List PlannedSummaryBlock) :
    ∀ count, (∀ index : Fin count, PlannedSummaryBlock.TraceLawfulAfter
      (trace.take (3 * index.val)) ((trace.drop (3 * index.val)).take 3)) →
      PlannedSummaryBlock.TraceLawfulAfter [] (trace.take (3 * count)) := by
  intro count
  induction count with
  | zero => intro _; trivial
  | succ count ih =>
      intro hchunks
      rw [Nat.mul_succ, List.take_add]
      apply (PlannedSummaryBlock.traceLawfulAfter_append [] _ _).mpr
      refine ⟨ih (fun index => hchunks index.castSucc), ?_⟩
      simpa using hchunks ⟨count, Nat.lt_succ_self count⟩

/-- Every stated nonempty-region start is exactly the allocator's least fit. -/
theorem actionSortedPlacementTrace_lawful :
    PlannedSummaryBlock.Lawful AllocationView.empty actionSortedPlacementTrace := by
  have hchunks (index : Fin 61) : PlannedSummaryBlock.TraceLawfulAfter
      (actionSortedPlacementTrace.take (3 * index.val))
      ((actionSortedPlacementTrace.drop (3 * index.val)).take 3) := by
    fin_cases index
    · exact traceChunk0
    · exact traceChunk3
    · exact traceChunk6
    · exact traceChunk9
    · exact traceChunk12
    · exact traceChunk15
    · exact traceChunk18
    · exact traceChunk21
    · exact traceChunk24
    · exact traceChunk27
    · exact traceChunk30
    · exact traceChunk33
    · exact traceChunk36
    · exact traceChunk39
    · exact traceChunk42
    · exact traceChunk45
    · exact traceChunk48
    · exact traceChunk51
    · exact traceChunk54
    · exact traceChunk57
    · exact traceChunk60
    · exact traceChunk63
    · exact traceChunk66
    · exact traceChunk69
    · exact traceChunk72
    · exact traceChunk75
    · exact traceChunk78
    · exact traceChunk81
    · exact traceChunk84
    · exact traceChunk87
    · exact traceChunk90
    · exact traceChunk93
    · exact traceChunk96
    · exact traceChunk99
    · exact traceChunk102
    · exact traceChunk105
    · exact traceChunk108
    · exact traceChunk111
    · exact traceChunk114
    · exact traceChunk117
    · exact traceChunk120
    · exact traceChunk123
    · exact traceChunk126
    · exact traceChunk129
    · exact traceChunk132
    · exact traceChunk135
    · exact traceChunk138
    · exact traceChunk141
    · exact traceChunk144
    · exact traceChunk147
    · exact traceChunk150
    · exact traceChunk153
    · exact traceChunk156
    · exact traceChunk159
    · exact traceChunk162
    · exact traceChunk165
    · exact traceChunk168
    · exact traceChunk171
    · exact traceChunk174
    · exact traceChunk177
    · exact traceChunk180
  have htrace := lawful_take_chunks actionSortedPlacementTrace 61 hchunks
  rw [List.take_of_length_le (by decide +kernel : actionSortedPlacementTrace.length ≤ 3 * 61)] at htrace
  simpa only [PlannedSummaryBlock.finalView] using
    PlannedSummaryBlock.lawful_of_traceLawfulAfter [] actionSortedPlacementTrace (by simp) htrace

end

/-- The complete ordered placement input, including the two empty regions. -/
def actionSortedPlacementShapes : List RegionShapeSummary :=
  PlannedSummaryBlock.summaries actionSortedPlacementTrace ++
    List.replicate 2 { columns := [], rowCount := 0 }

/-- Every individual start from the certified blocks, followed by the empty-region starts. -/
def actionSortedPlacementStarts : List ℕ :=
  plannerTraceStarts actionSortedPlacementTrace ++ List.replicate 2 0

/-- The allocator computes exactly the certified list of all 395 starts in this order. -/
theorem actionSortedPlacementStarts_eq_slot :
    (slotShapeSummariesFrom actionSortedPlacementShapes ∅).1 = actionSortedPlacementStarts := by
  have hstarts := slotShapeSummariesFrom_trace_starts actionSortedPlacementTrace ∅ AllocationView.empty
    (by intro column; simp [AllocationView.empty]) (by intro column; exact List.Pairwise.nil)
    actionSortedPlacementTrace_lawful
  unfold actionSortedPlacementShapes actionSortedPlacementStarts
  simp only [slotShapeSummariesFrom_append, slotShapeSummariesFrom_replicate_empty_starts]
  exact congrArg (fun starts => starts ++ List.replicate 2 0) hstarts.1

/-- The placement certificate retains the complete source region count. -/
theorem actionSortedPlacementShapes_length : actionSortedPlacementShapes.length = 395 := by
  decide +kernel

end Zcash.Snark.ZeroKnowledge
