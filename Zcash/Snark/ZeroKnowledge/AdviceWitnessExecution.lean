import Clean.Halo2.Operations

/-!
# Executing advice witness programs at the circuit's placement

Fixed cells and public inputs are supplied by the compiled environment. Advice
programs are evaluated in source order against the current assignment, then their
single result is written at the placed target cell. This module defines execution
and its frame properties; satisfaction of the final witness equations additionally
requires the programs' read-dependency and write-consistency proofs.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- One actual advice program and its absolute target under the floor planner. -/
structure PlacedAdviceProgram (F : Type) where
  column : Column .advice
  row : ℕ
  program : WitgenIR F 1

/-- Extract a region's advice programs in their original execution order. -/
def regionAdvicePrograms {F : Type} (place : RegionIndex → ℕ) (region : RegionIndex) :
    RegionOperations F → List (PlacedAdviceProgram F)
  | [] => []
  | .assignAdvice column row program :: rest =>
      ⟨column, place region + row, program⟩ :: regionAdvicePrograms place region rest
  | _ :: rest => regionAdvicePrograms place region rest

/-- Extract the complete circuit's programs while threading the actual region counter. -/
def circuitAdvicePrograms {F : Type} (place : RegionIndex → ℕ) :
    Operations F → RegionIndex → List (PlacedAdviceProgram F)
  | [], _ => []
  | .region _ programs :: rest, region =>
      regionAdvicePrograms place region programs ++ circuitAdvicePrograms place rest (region + 1)
  | _ :: rest, region => circuitAdvicePrograms place rest region

/-- Write one advice value, preserving all other cells, layout metadata, and prover hints. -/
def writeAdviceValue {F : Type} (environment : ProverEnvironment F)
    (column : Column .advice) (row : ℕ) (value : F) : ProverEnvironment F :=
  { environment with
    get := fun queried absoluteRow =>
      if queried = column.toAny ∧ absoluteRow = (row : ℤ) then value else environment.get queried absoluteRow }

/-- Run the extracted witness programs using the same placed evaluation as `ExtendsWitnesses`. -/
def runAdvicePrograms {F : Type} [FiniteField F] (place : RegionIndex → ℕ) :
    List (PlacedAdviceProgram F) → ProverEnvironment F → ProverEnvironment F
  | [], environment => environment
  | instruction :: rest, environment =>
      runAdvicePrograms place rest (writeAdviceValue environment instruction.column instruction.row
        ((instruction.program.eval ⟨place, environment⟩)[0]))

/-- Writing an advice cell installs exactly the computed value at that cell. -/
theorem writeAdviceValue_get_target {F : Type} (environment : ProverEnvironment F)
    (column : Column .advice) (row : ℕ) (value : F) :
    (writeAdviceValue environment column row value).get column.toAny (row : ℤ) = value := by
  simp only [writeAdviceValue, and_self, if_true]

/-- An advice write cannot change a different cell. -/
theorem writeAdviceValue_get_frame {F : Type} (environment : ProverEnvironment F)
    (column : Column .advice) (row : ℕ) (value : F) (queried : AnyColumn) (absoluteRow : ℤ)
    (hframe : ¬(queried = column.toAny ∧ absoluteRow = (row : ℤ))) :
    (writeAdviceValue environment column row value).get queried absoluteRow = environment.get queried absoluteRow := by
  simp only [writeAdviceValue, if_neg hframe]

/-- The complete execution leaves every untargeted cell unchanged. -/
theorem runAdvicePrograms_get_frame {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (PlacedAdviceProgram F)) (environment : ProverEnvironment F)
    (queried : AnyColumn) (absoluteRow : ℤ)
    (hframe : ∀ instruction ∈ programs,
      ¬(queried = instruction.column.toAny ∧ absoluteRow = (instruction.row : ℤ))) :
    (runAdvicePrograms place programs environment).get queried absoluteRow = environment.get queried absoluteRow := by
  induction programs generalizing environment with
  | nil => rfl
  | cons instruction rest ih =>
    rw [runAdvicePrograms, ih _ (fun next hnext => hframe next (List.mem_cons_of_mem _ hnext))]
    exact writeAdviceValue_get_frame _ _ _ _ _ _ (hframe instruction (List.mem_cons_self))

/-- Advice execution never changes a fixed or instance column. -/
theorem runAdvicePrograms_get_nonadvice {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (PlacedAdviceProgram F)) (environment : ProverEnvironment F)
    (queried : AnyColumn) (absoluteRow : ℤ) (hkind : queried.kind ≠ .advice) :
    (runAdvicePrograms place programs environment).get queried absoluteRow = environment.get queried absoluteRow := by
  apply runAdvicePrograms_get_frame
  intro instruction _ hsame
  exact hkind (congrArg AnyColumn.kind hsame.1)

/-- The witness interpreter preserves the supplied hint store exactly. -/
theorem runAdvicePrograms_hint {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (PlacedAdviceProgram F)) (environment : ProverEnvironment F) :
    (runAdvicePrograms place programs environment).hint = environment.hint := by
  induction programs generalizing environment with
  | nil => rfl
  | cons instruction rest ih =>
    rw [runAdvicePrograms, ih]
    rfl

/-- The compiled usable-row bound is unchanged by executing advice programs. -/
theorem runAdvicePrograms_usableRows {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (PlacedAdviceProgram F)) (environment : ProverEnvironment F) :
    (runAdvicePrograms place programs environment).usableRows = environment.usableRows := by
  induction programs generalizing environment with
  | nil => rfl
  | cons instruction rest ih =>
    rw [runAdvicePrograms, ih]
    rfl

end Zcash.Snark.ZeroKnowledge
