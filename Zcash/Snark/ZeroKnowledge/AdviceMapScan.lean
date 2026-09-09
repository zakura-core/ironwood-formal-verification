import Zcash.Snark.ZeroKnowledge.AdviceSupportMapPlan

/-!
# Individual steps of the original advice-map checks

The option-valued step exposes the exact map carried to the next source entry.
It permits a kernel-checked scan to store intermediate maps without changing
either the read-availability policy or the repeated-write policy.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- Scan the original entries, rejecting precisely when one map step fails. -/
def adviceMapScan {α : Type} (step : AdviceAliasMap → α → Option AdviceAliasMap) :
    AdviceAliasMap → List α → Bool
  | _, [] => true
  | roots, entry :: rest =>
    match step roots entry with
    | none => false
    | some next => adviceMapScan step next rest

/-- A checked transition and the remaining scan establish the original scan. -/
theorem adviceMapScan_cons {α : Type} (step : AdviceAliasMap → α → Option AdviceAliasMap)
    (roots next : AdviceAliasMap) (entry : α) (rest : List α)
    (hstep : step roots entry = some next) (htail : adviceMapScan step next rest = true) :
    adviceMapScan step roots (entry :: rest) = true := by
  simp only [adviceMapScan, hstep]
  exact htail

/-- One original read check followed by insertion of the original target. -/
def adviceReadMapStep {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (roots : AdviceAliasMap) (entry : SupportedAdviceProgram F) : Option AdviceAliasMap :=
  if entry.reads.all (adviceCellReadMapAvailable place roots) then
    some (adviceAliasMapInsert roots (adviceProgramTarget entry.instruction)
      (adviceProgramTarget entry.instruction))
  else none

/-- The stepwise read scan returns exactly the original read-plan result. -/
theorem adviceSupportMapPlan_eq_scan {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (roots : AdviceAliasMap) (entries : List (SupportedAdviceProgram F)) :
    adviceSupportMapPlan place roots entries = adviceMapScan (adviceReadMapStep place) roots entries := by
  induction entries generalizing roots with
  | nil => rfl
  | cons entry rest ih =>
    simp only [adviceSupportMapPlan, adviceMapScan, adviceReadMapStep]
    cases entry.reads.all (adviceCellReadMapAvailable place roots) <;> simp [ih]

/-- One original freshness or equal-root-copy check, retaining all rejection branches. -/
def adviceAliasMapStep (roots : AdviceAliasMap)
    (entry : AdviceAddress × Option AdviceAddress) : Option AdviceAliasMap :=
  match entry with
  | (target, none) =>
    match adviceAliasMapLookup roots target with
    | some _ => none
    | none => some (adviceAliasMapInsert roots target target)
  | (target, some source) =>
    if (adviceAliasMapLookup roots source).isSome = true ∨ source.1.kind ≠ .advice then
      let sourceRoot := (adviceAliasMapLookup roots source).getD source
      match adviceAliasMapLookup roots target with
      | some targetRoot => if targetRoot = sourceRoot then some roots else none
      | none => some (adviceAliasMapInsert roots target sourceRoot)
    else none

/-- The stepwise alias scan returns exactly the original repeated-write-plan result. -/
theorem adviceAliasMapPlan_eq_scan (roots : AdviceAliasMap)
    (entries : List (AdviceAddress × Option AdviceAddress)) :
    adviceAliasMapPlan roots entries = adviceMapScan adviceAliasMapStep roots entries := by
  induction entries generalizing roots with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨target, source⟩
    cases source with
    | none =>
      simp only [adviceAliasMapPlan, adviceMapScan, adviceAliasMapStep]
      cases adviceAliasMapLookup roots target <;> simp [ih]
    | some source =>
      by_cases hsource : (adviceAliasMapLookup roots source).isSome = true ∨ source.1.kind ≠ .advice
      · simp only [adviceAliasMapPlan, adviceMapScan, adviceAliasMapStep, if_pos hsource]
        cases htarget : adviceAliasMapLookup roots target with
        | none => exact ih _
        | some targetRoot =>
          by_cases hroot : targetRoot = (adviceAliasMapLookup roots source).getD source
          · simp only [if_pos hroot, ih]
          · simp only [if_neg hroot]
      · simp only [adviceAliasMapPlan, adviceMapScan, adviceAliasMapStep, if_neg hsource]

end Zcash.Snark.ZeroKnowledge
