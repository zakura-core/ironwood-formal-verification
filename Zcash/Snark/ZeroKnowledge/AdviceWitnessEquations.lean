import Zcash.Snark.ZeroKnowledge.AdviceWitnessCausality

/-!
# Decomposing the source circuit's witness equations

Erasing only advice assignments leaves the fixed-write and table clauses of
`ExtendsWitnesses`. The advice clauses are exactly the equations for the collected
placed programs. This relates the execution certificate to the existing circuit
semantics while preserving every region index and the original fixed-data checks.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Remove advice writes from a region while retaining its fixed operations and layout. -/
def eraseRegionAdvice {F : Type} : RegionOperations F → RegionOperations F
  | [] => []
  | .assignAdvice _ _ _ :: rest => eraseRegionAdvice rest
  | operation :: rest => operation :: eraseRegionAdvice rest

/-- Remove advice writes from a circuit without changing its region count or fixed table loads. -/
def eraseCircuitAdvice {F : Type} : Operations F → Operations F
  | [] => []
  | .region name programs :: rest => .region name (eraseRegionAdvice programs) :: eraseCircuitAdvice rest
  | operation :: rest => operation :: eraseCircuitAdvice rest

/-- Advice equations for concatenated fragments are exactly both fragments' equations. -/
theorem adviceWitnessEquations_append {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (left right : List (PlacedAdviceProgram F)) (environment : ProverEnvironment F) :
    AdviceWitnessEquations place (left ++ right) environment ↔
      AdviceWitnessEquations place left environment ∧ AdviceWitnessEquations place right environment := by
  simp only [AdviceWitnessEquations, List.mem_append, or_imp, forall_and]

/-- The region's original witness semantics splits into actual advice programs and retained fixed checks. -/
theorem regionWitnessEquations_iff {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (region : RegionIndex) (programs : RegionOperations F)
    (environment : ProverEnvironment F) :
    RegionOperations.ExtendsWitnesses place region environment programs ↔
      AdviceWitnessEquations place (regionAdvicePrograms place region programs) environment ∧
        RegionOperations.ExtendsWitnesses place region environment (eraseRegionAdvice programs) := by
  induction programs with
  | nil => simp [RegionOperations.ExtendsWitnesses, regionAdvicePrograms, AdviceWitnessEquations, eraseRegionAdvice]
  | cons operation rest ih =>
    cases operation <;>
      simp [RegionOperations.ExtendsWitnesses, RegionOperation.ExtendsWitness,
        regionAdvicePrograms, eraseRegionAdvice, AdviceWitnessEquations] at ih ⊢ <;>
      tauto

/-- The complete source witness semantics is exactly the collected advice equations and fixed-data checks. -/
theorem circuitWitnessEquations_iff {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (programs : Operations F) (region : RegionIndex)
    (environment : ProverEnvironment F) :
    ExtendsWitnesses place environment programs region ↔
      AdviceWitnessEquations place (circuitAdvicePrograms place programs region) environment ∧
        ExtendsWitnesses place environment (eraseCircuitAdvice programs) region := by
  induction programs generalizing region with
  | nil => simp [ExtendsWitnesses, circuitAdvicePrograms, eraseCircuitAdvice, AdviceWitnessEquations]
  | cons operation rest ih =>
    cases operation with
    | region name programs =>
      simp only [ExtendsWitnesses, circuitAdvicePrograms, eraseCircuitAdvice,
        adviceWitnessEquations_append]
      rw [regionWitnessEquations_iff place region programs environment, ih (region + 1)]
      tauto
    | constrainInstance cell column row =>
      simpa only [ExtendsWitnesses, circuitAdvicePrograms, eraseCircuitAdvice] using ih region
    | loadTable table values =>
      simp only [ExtendsWitnesses, circuitAdvicePrograms, eraseCircuitAdvice, ih]
      tauto

/-- Equal fixed cells suffice for the advice-erased region's witness clauses. -/
theorem eraseRegionAdvice_extends_congr {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (region : RegionIndex) (programs : RegionOperations F)
    (left right : ProverEnvironment F)
    (hfixed : ∀ column row, left.fixed column row = right.fixed column row) :
    RegionOperations.ExtendsWitnesses place region left (eraseRegionAdvice programs) ↔
      RegionOperations.ExtendsWitnesses place region right (eraseRegionAdvice programs) := by
  have hget : ∀ (column : Column .fixed) (row : ℤ),
      left.get column.toAny row = right.get column.toAny row := hfixed
  induction programs with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;>
      simp only [eraseRegionAdvice, RegionOperations.ExtendsWitnesses, RegionOperation.ExtendsWitness,
        hget, ih, true_and]

/-- Equal fixed columns and row bounds suffice for all advice-erased witness and table clauses. -/
theorem eraseCircuitAdvice_extends_congr {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (programs : Operations F) (region : RegionIndex)
    (left right : ProverEnvironment F)
    (hfixed : ∀ column row, left.fixed column row = right.fixed column row)
    (hrows : left.usableRows = right.usableRows) :
    ExtendsWitnesses place left (eraseCircuitAdvice programs) region ↔
      ExtendsWitnesses place right (eraseCircuitAdvice programs) region := by
  induction programs generalizing region with
  | nil => rfl
  | cons operation rest ih =>
    cases operation with
    | region name programs =>
      simp only [eraseCircuitAdvice, ExtendsWitnesses, ih,
        eraseRegionAdvice_extends_congr place region programs left right hfixed]
    | constrainInstance cell column row =>
      exact ih region
    | loadTable table values =>
      simp only [eraseCircuitAdvice, ExtendsWitnesses, hfixed, hrows, ih]

/-- Executing advice preserves every fixed-write and table requirement of the original source. -/
theorem runAdvicePrograms_fixedWitnesses {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (instructions : List (PlacedAdviceProgram F))
    (environment : ProverEnvironment F) (programs : Operations F) (region : RegionIndex) :
    ExtendsWitnesses place (runAdvicePrograms place instructions environment) (eraseCircuitAdvice programs) region ↔
      ExtendsWitnesses place environment (eraseCircuitAdvice programs) region := by
  apply eraseCircuitAdvice_extends_congr
  · intro column row
    exact runAdvicePrograms_get_nonadvice place instructions environment column.toAny row
      (by change ColumnKind.fixed ≠ .advice; decide)
  · exact runAdvicePrograms_usableRows place instructions environment

/-- Structural read/write certificates and the compiled fixed environment establish full witness extension. -/
theorem runCircuitAdvice_extendsWitnesses {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (programs : Operations F) (region : RegionIndex)
    (environment : ProverEnvironment F)
    (hcausal : AdviceProgramsCausal place [] (circuitAdvicePrograms place programs region))
    (hnodup : ((circuitAdvicePrograms place programs region).map adviceProgramTarget).Nodup)
    (hfixed : ExtendsWitnesses place environment (eraseCircuitAdvice programs) region) :
    ExtendsWitnesses place
      (runAdvicePrograms place (circuitAdvicePrograms place programs region) environment) programs region := by
  apply (circuitWitnessEquations_iff place programs region _).mpr
  constructor
  · exact runAdvicePrograms_satisfies place [] _ environment hcausal hnodup (by simp)
  · exact (runAdvicePrograms_fixedWitnesses place _ environment programs region).mpr hfixed

end Zcash.Snark.ZeroKnowledge
