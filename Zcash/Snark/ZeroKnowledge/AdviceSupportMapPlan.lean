import Zcash.Snark.ZeroKnowledge.AdviceAliasMapPlan
import Zcash.Snark.ZeroKnowledge.AdviceSupportPlan

/-!
# Finite-map checks for certified witness reads

The map records availability at the original source position. Each annotation
still needs its semantic support proof. Together with the refined alias check,
the same compiler witness-equation theorem can use finite-map certificates.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- An immutable cell or a previously established advice address may be read. -/
def adviceCellReadMapAvailable {F : Type} (place : RegionIndex → ℕ)
    (roots : AdviceAliasMap) (cell : AssignedCell F) : Bool :=
  decide (cell.cell.column.kind ≠ .advice ∨
    (adviceAliasMapLookup roots (placedWitnessCell place cell)).isSome = true)

/-- Map availability is exactly the original source-position read check. -/
theorem adviceCellReadMapAvailable_eq {F : Type} (place : RegionIndex → ℕ)
    (roots : AdviceAliasMap) (available : List AdviceAddress) (root : AdviceAddress → AdviceAddress)
    (represents : AdviceAliasMapRepresents roots available root) (cell : AssignedCell F) :
    adviceCellReadMapAvailable place roots cell = adviceCellReadAvailable place available cell := by
  simp [adviceCellReadMapAvailable, adviceCellReadAvailable, represents.known]

/-- Check all certified reads before recording the original instruction's target. -/
def adviceSupportMapPlan {F : Type} [FiniteField F] (place : RegionIndex → ℕ) :
    AdviceAliasMap → List (SupportedAdviceProgram F) → Bool
  | _, [] => true
  | roots, annotated :: rest =>
    annotated.reads.all (adviceCellReadMapAvailable place roots) &&
      adviceSupportMapPlan place
        (adviceAliasMapInsert roots (adviceProgramTarget annotated.instruction)
          (adviceProgramTarget annotated.instruction)) rest

/-- The finite-map read scan preserves every result of the original certified scan. -/
theorem adviceSupportMapPlan_eq {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (SupportedAdviceProgram F)) (roots : AdviceAliasMap)
    (available : List AdviceAddress) (root : AdviceAddress → AdviceAddress)
    (represents : AdviceAliasMapRepresents roots available root) :
    adviceSupportMapPlan place roots programs = adviceSupportPlan place available programs := by
  induction programs generalizing roots available root with
  | nil => rfl
  | cons annotated rest ih =>
    have havailable : adviceCellReadMapAvailable place roots =
        adviceCellReadAvailable (F := F) place available :=
      funext (adviceCellReadMapAvailable_eq place roots available root represents)
    simp only [adviceSupportMapPlan, adviceSupportPlan, havailable]
    rw [ih _ _ _ (represents.insert (adviceProgramTarget annotated.instruction)
      (adviceProgramTarget annotated.instruction))]

/-- A successful map scan establishes causality for the unchanged original instructions. -/
theorem adviceSupportMapPlan_causal {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (SupportedAdviceProgram F))
    (hcheck : adviceSupportMapPlan place ∅ programs = true) :
    AdviceProgramsCausal place [] (programs.map SupportedAdviceProgram.instruction) := by
  rw [adviceSupportMapPlan_eq _ _ _ _ _ adviceAliasMapRepresents_empty] at hcheck
  exact adviceSupportPlan_causal place programs [] hcheck

/-- The two refined checks and exact source certificates establish the original witness equations. -/
theorem topLevelAdviceAssignment_extendsWitnesses_of_mapPlans
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (circuit : TopLevelCircuit Fp Config PublicInput) (initial : ProofAssignment Fp) (hints : ProverHint Fp)
    (aliases : List (PlacedAdviceProgram Fp × Option AdviceAddress))
    (programs : List (SupportedAdviceProgram Fp))
    (haliases : aliases.map Prod.fst = circuitAdvicePrograms circuit.placement circuit.operations 0)
    (hprograms : programs.map SupportedAdviceProgram.instruction = aliases.map Prod.fst)
    (haliasCheck : adviceAliasMapPlan ∅ (adviceAliasAddressData aliases) = true)
    (hreadCheck : adviceSupportMapPlan circuit.placement ∅ programs = true)
    (hsources : AdviceAliasSources circuit.placement aliases) :
    ExtendsWitnesses circuit.placement
      (circuit.proverEnvironment (topLevelAdviceAssignment circuit initial hints) hints)
      circuit.operations 0 := by
  rw [adviceAliasMapPlan_original] at haliasCheck
  rw [adviceSupportMapPlan_eq _ _ _ _ _ adviceAliasMapRepresents_empty] at hreadCheck
  exact topLevelAdviceAssignment_extendsWitnesses_of_supportPlan circuit initial hints
    aliases programs haliases hprograms haliasCheck hreadCheck hsources

end Zcash.Snark.ZeroKnowledge
