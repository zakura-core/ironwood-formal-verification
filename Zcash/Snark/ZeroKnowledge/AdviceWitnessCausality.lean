import Zcash.Snark.ZeroKnowledge.AdviceWitnessExecution

/-!
# Read-dependency certificates for advice witness execution

A program may depend on the fixed environment, public inputs, hints, and already
available advice cells. If targets are distinct and fresh, later writes cannot
change those reads. The final assignment therefore satisfies every advice witness
equation. Applying this result to Action requires its actual structural certificate;
no circuit constraint or successful execution is assumed by the generic theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- The absolute address targeted by one placed advice instruction. -/
def adviceProgramTarget {F : Type} (instruction : PlacedAdviceProgram F) : AnyColumn × ℤ :=
  (instruction.column.toAny, instruction.row)

/-- Agreement on immutable inputs and the advice cells available to a witness program. -/
structure AdviceReadAgreement {F : Type} (available : List (AnyColumn × ℤ))
    (left right : ProverEnvironment F) : Prop where
  hints : left.hint = right.hint
  rows : left.usableRows = right.usableRows
  nonAdvice : ∀ column row, column.kind ≠ .advice → left.get column row = right.get column row
  advice : ∀ address ∈ available, left.get address.1 address.2 = right.get address.1 address.2

/-- A program's value depends only on the declared earlier cells and immutable inputs. -/
def AdviceProgramReadsFrom {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (available : List (AnyColumn × ℤ)) (program : WitgenIR F 1) : Prop :=
  ∀ left right, AdviceReadAgreement available left right →
    (program.eval ⟨place, left⟩)[0] = (program.eval ⟨place, right⟩)[0]

/-- Each program reads only immutable inputs and advice written before its own target. -/
def AdviceProgramsCausal {F : Type} [FiniteField F] (place : RegionIndex → ℕ) :
    List (AnyColumn × ℤ) → List (PlacedAdviceProgram F) → Prop
  | _, [] => True
  | available, instruction :: rest =>
      AdviceProgramReadsFrom place available instruction.program ∧
        AdviceProgramsCausal place (adviceProgramTarget instruction :: available) rest

/-- The final assignment agrees with every original advice witness program evaluated in that assignment. -/
def AdviceWitnessEquations {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (PlacedAdviceProgram F)) (environment : ProverEnvironment F) : Prop :=
  ∀ instruction ∈ programs,
    environment.get instruction.column.toAny (instruction.row : ℤ) =
      (instruction.program.eval ⟨place, environment⟩)[0]

/-- Future writes preserve all previously available reads when their targets are disjoint. -/
theorem runAdvicePrograms_readAgreement {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (available : List (AnyColumn × ℤ))
    (programs : List (PlacedAdviceProgram F)) (environment : ProverEnvironment F)
    (hdisjoint : ∀ address ∈ available, ∀ instruction ∈ programs,
      address ≠ adviceProgramTarget instruction) :
    AdviceReadAgreement available environment (runAdvicePrograms place programs environment) := by
  constructor
  · exact (runAdvicePrograms_hint place programs environment).symm
  · exact (runAdvicePrograms_usableRows place programs environment).symm
  · intro column row hkind
    exact (runAdvicePrograms_get_nonadvice place programs environment column row hkind).symm
  · intro address haddress
    symm
    apply runAdvicePrograms_get_frame
    intro instruction hinstruction hsame
    exact hdisjoint address haddress instruction hinstruction (Prod.ext hsame.1 hsame.2)

/-- Causal programs with distinct fresh targets produce a final assignment satisfying all advice equations. -/
theorem runAdvicePrograms_satisfies {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (available : List (AnyColumn × ℤ))
    (programs : List (PlacedAdviceProgram F)) (environment : ProverEnvironment F)
    (hcausal : AdviceProgramsCausal place available programs)
    (hnodup : (programs.map adviceProgramTarget).Nodup)
    (hdisjoint : ∀ address ∈ available, ∀ instruction ∈ programs,
      address ≠ adviceProgramTarget instruction) :
    AdviceWitnessEquations place programs (runAdvicePrograms place programs environment) := by
  induction programs generalizing available environment with
  | nil => intro instruction h; cases h
  | cons instruction rest ih =>
    obtain ⟨hread, hcausalRest⟩ := hcausal
    obtain ⟨hfresh, hnodupRest⟩ := List.nodup_cons.mp hnodup
    let updated := writeAdviceValue environment instruction.column instruction.row
      ((instruction.program.eval ⟨place, environment⟩)[0])
    have hdisjointRest : ∀ address ∈ adviceProgramTarget instruction :: available,
        ∀ next ∈ rest, address ≠ adviceProgramTarget next := by
      intro address haddress next hnext
      rcases List.mem_cons.mp haddress with rfl | hold
      · intro heq
        exact hfresh (List.mem_map.mpr ⟨next, hnext, heq.symm⟩)
      · exact hdisjoint address hold next (List.mem_cons_of_mem _ hnext)
    have hrest := ih (adviceProgramTarget instruction :: available) updated hcausalRest hnodupRest hdisjointRest
    intro selected hselected
    rcases List.mem_cons.mp hselected with hselected | hinrest
    · subst selected
      change (runAdvicePrograms place rest updated).get instruction.column.toAny (instruction.row : ℤ) = _
      calc
        _ = updated.get instruction.column.toAny (instruction.row : ℤ) := by
          apply runAdvicePrograms_get_frame
          intro next hnext hsame
          exact hdisjointRest (adviceProgramTarget instruction) (List.mem_cons_self) next hnext
            (Prod.ext hsame.1 hsame.2)
        _ = (instruction.program.eval ⟨place, environment⟩)[0] := writeAdviceValue_get_target _ _ _ _
        _ = _ := hread environment (runAdvicePrograms place (instruction :: rest) environment)
          (runAdvicePrograms_readAgreement place available (instruction :: rest) environment hdisjoint)
    · exact hrest selected hinrest

end Zcash.Snark.ZeroKnowledge
