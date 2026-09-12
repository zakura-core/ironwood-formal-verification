import Zcash.Snark.ZeroKnowledge.ActionWitnessRows
import Zcash.Circuits.Action.PlannerTrace

/-!
# The original advice footprint and zero padding

Every interpreter write retains its original instruction and region. V1 placement
therefore bounds its target, and the execution frame law leaves every other cell
unchanged. The actual Action assignment is zero before row zero and from row 1779
onward, independently of the witness and its semantic validity.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

/-- Every collected advice write retains its exact original region instruction. -/
theorem mem_regionAdvicePrograms_iff {F : Type} (place : RegionIndex → ℕ)
    (region : RegionIndex) (body : RegionOperations F) (instruction : PlacedAdviceProgram F) :
    instruction ∈ regionAdvicePrograms place region body ↔
      ∃ localRow, RegionOperation.assignAdvice instruction.column localRow instruction.program ∈ body ∧
        instruction.row = place region + localRow := by
  rcases instruction with ⟨column, row, program⟩
  induction body with
  | nil => simp [regionAdvicePrograms]
  | cons operation rest ih =>
    cases operation <;> simp_all [regionAdvicePrograms]
    all_goals aesop

/-- Collection threads the original region counter without changing any target. -/
theorem mem_circuitAdvicePrograms_iff {F : Type} (place : RegionIndex → ℕ)
    (operations : Operations F) (initial : RegionIndex) (instruction : PlacedAdviceProgram F) :
    instruction ∈ circuitAdvicePrograms place operations initial ↔
      ∃ region body localRow,
        (region, body) ∈ (indexedRegions operations initial).1 ∧
        RegionOperation.assignAdvice instruction.column localRow instruction.program ∈ body ∧
        instruction.row = place region + localRow := by
  induction operations generalizing initial with
  | nil => simp [circuitAdvicePrograms, indexedRegions]
  | cons operation rest ih =>
    cases operation <;>
      simp_all [circuitAdvicePrograms, indexedRegions, mem_regionAdvicePrograms_iff]
    all_goals aesop

/-- Original V1 advice targets lie below the proved placed-region endpoint. -/
theorem circuitAdvicePrograms_row_lt_placementEnd {F : Type}
    (operations : Operations F) (instruction : PlacedAdviceProgram F)
    (hinstruction : instruction ∈ circuitAdvicePrograms
      (fun region => (FloorPlanner.V1.starts operations).getD region 0) operations 0) :
    instruction.row < FloorPlanner.V1.placementEnd operations := by
  obtain ⟨region, body, localRow, hregion, hoperation, hrow⟩ :=
    (mem_circuitAdvicePrograms_iff _ operations 0 instruction).mp hinstruction
  have hshape : FloorPlanner.measureRegion region body ∈ FloorPlanner.measureRegions operations :=
    List.mem_map.mpr ⟨(region, body), hregion, rfl⟩
  have hend := FloorPlanner.V1.shape_end_le_placementEndFrom_of_mem
    (FloorPlanner.measureRegions operations) (FloorPlanner.V1.starts operations)
    (FloorPlanner.measureRegion region body) hshape
  have hlocal := FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
    body (.assignAdvice instruction.column localRow instruction.program) hoperation
  simp only [FloorPlanner.regionOperationRowExtent] at hlocal
  change _ ≤ FloorPlanner.V1.placementEnd operations at hend
  simp only [FloorPlanner.measureRegion] at hend
  omega

/-- Generated advice remains zero before row zero and after its source footprint. -/
theorem topLevelAdviceAssignment_advice_zero_of_outside
    {F : Type} [FiniteField F] {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) (inputs : PublicInput F) (hints : ProverHint F)
    (column : Column .advice) (row : ℤ)
    (hrow : row < 0 ∨ (FloorPlanner.V1.placementEnd top.operations : ℤ) ≤ row) :
    (topLevelAdviceAssignment top (initialPublicWitnessAssignment top inputs) hints).advice column row = 0 := by
  change (runAdvicePrograms top.placement (circuitAdvicePrograms top.placement top.operations 0)
    (top.proverEnvironment (initialPublicWitnessAssignment top inputs) hints)).get column.toAny row = 0
  rw [runAdvicePrograms_get_frame]
  · rfl
  · intro instruction hinstruction hequal
    have hbound := circuitAdvicePrograms_row_lt_placementEnd top.operations instruction hinstruction
    omega

/-- The actual Action constructor has zero advice outside rows 0 through 1778. -/
theorem actionWitnessAssignment_advice_zero_of_outside
    (inputs : PublicInputs Fp) (witness : PrivateWitness) (column : Column .advice) (row : ℤ)
    (hrow : row < 0 ∨ 1779 ≤ row) :
    (actionWitnessAssignment inputs witness).advice column row = 0 := by
  apply topLevelAdviceAssignment_advice_zero_of_outside
  rwa [actionCircuit_placementEnd_eq_1779]

end Zcash.Snark.ZeroKnowledge
