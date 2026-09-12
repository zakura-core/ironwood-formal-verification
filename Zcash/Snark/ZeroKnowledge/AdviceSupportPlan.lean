import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Snark.ZeroKnowledge.AdviceReadPlan
import Zcash.Snark.ZeroKnowledge.AdviceAliasPlan

/-!
# Checking a program list with certified read annotations

Each annotation contains its original instruction and a semantic support proof.
The Boolean scan checks availability at the exact source position. Erasure must
match the original circuit program list before this result can establish witness
extension. Native callbacks and structured IR use the same checked interface.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen

/-- An original instruction together with a proved sufficient set of cell reads. -/
structure SupportedAdviceProgram (F : Type) [FiniteField F] where
  instruction : PlacedAdviceProgram F
  reads : List (AssignedCell F)
  support : WitnessFunctionSupport reads (fun env => (instruction.program.eval env)[0])

/-- Attach a native or structured function certificate without changing the instruction. -/
def supportedAdviceProgram {F : Type} [FiniteField F] (instruction : PlacedAdviceProgram F)
    (reads : List (AssignedCell F))
    (support : WitnessFunctionSupport reads (fun env => (instruction.program.eval env)[0])) :
    SupportedAdviceProgram F := ⟨instruction, reads, support⟩

/-- The complete structured collector supplies the same interface without an extra premise. -/
def supportedStructuredAdvice {F : Type} [FiniteField F] (column : Column .advice) (row : ℕ)
    (steps : List (StepOver F (AssignedCell F))) (output : VExprOver F (AssignedCell F) 1) :
    SupportedAdviceProgram F where
  instruction := ⟨column, row, .ir steps output⟩
  reads := stepsWitnessReads steps ++ vectorWitnessReads output
  support := fun left right agreement => congrArg (fun values : Vector F 1 => values[0])
    (structuredWitnessReads_eval steps output left right agreement)

/-- Check all certified reads before adding the original instruction's target. -/
def adviceSupportPlan {F : Type} [FiniteField F] (place : RegionIndex → ℕ) :
    List AdviceAddress → List (SupportedAdviceProgram F) → Bool
  | _, [] => true
  | available, annotated :: rest =>
    annotated.reads.all (adviceCellReadAvailable place available) &&
      adviceSupportPlan place (adviceProgramTarget annotated.instruction :: available) rest

/-- Success proves every original instruction's semantic read-order obligation. -/
theorem adviceSupportPlan_causal {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (SupportedAdviceProgram F)) (available : List AdviceAddress)
    (hcheck : adviceSupportPlan place available programs = true) :
    AdviceProgramsCausal place available (programs.map SupportedAdviceProgram.instruction) := by
  induction programs generalizing available with
  | nil => trivial
  | cons annotated rest ih =>
    obtain ⟨hreads, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
    constructor
    · apply witnessFunctionSupport_readsFrom place available annotated.reads annotated.instruction.program annotated.support
      intro cell hcell hadvice
      have h := of_decide_eq_true ((List.all_eq_true.mp hreads) cell hcell)
      exact h.resolve_left (by simp [hadvice])
    · exact ih _ hrest

/-- Two finite checks and exact source erasure establish all original compiler witness equations. -/
theorem topLevelAdviceAssignment_extendsWitnesses_of_supportPlan
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (circuit : TopLevelCircuit Fp Config PublicInput) (initial : ProofAssignment Fp) (hints : ProverHint Fp)
    (aliases : List (PlacedAdviceProgram Fp × Option AdviceAddress))
    (programs : List (SupportedAdviceProgram Fp))
    (haliases : aliases.map Prod.fst = circuitAdvicePrograms circuit.placement circuit.operations 0)
    (hprograms : programs.map SupportedAdviceProgram.instruction = aliases.map Prod.fst)
    (haliasCheck : adviceAliasPlan [] id aliases = true)
    (hreadCheck : adviceSupportPlan circuit.placement [] programs = true)
    (hsources : AdviceAliasSources circuit.placement aliases) :
    ExtendsWitnesses circuit.placement
      (circuit.proverEnvironment (topLevelAdviceAssignment circuit initial hints) hints)
      circuit.operations 0 := by
  apply topLevelAdviceAssignment_extendsWitnesses_of_aliasPlan circuit initial hints aliases haliases haliasCheck
  · rw [← hprograms]
    exact adviceSupportPlan_causal circuit.placement programs [] hreadCheck
  · exact hsources

end Zcash.Snark.ZeroKnowledge
