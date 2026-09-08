import Zcash.Snark.ZeroKnowledge.CompiledFixedWitnesses

/-!
# Advice execution with certified repeated writes

A local invariant may track copy equalities. Each step must read only available
advice and preserve the values of all cells already available. Fresh writes and
value-preserving repeated writes both satisfy this rule. The final theorem
establishes every original witness equation without a distinct-target premise.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Execute one placed instruction using exactly the existing scalar evaluator. -/
def runAdviceInstruction {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (instruction : PlacedAdviceProgram F) (environment : ProverEnvironment F) : ProverEnvironment F :=
  writeAdviceValue environment instruction.column instruction.row
    ((instruction.program.eval ⟨place, environment⟩)[0])

/-- Each local proof preserves established cell values and advances a named invariant. -/
inductive AdviceTraceCertificate {F : Type} [FiniteField F] (place : RegionIndex → ℕ) :
    List (AnyColumn × ℤ) → (ProverEnvironment F → Prop) → List (PlacedAdviceProgram F) → Prop where
  | nil (available : List (AnyColumn × ℤ)) (invariant : ProverEnvironment F → Prop) :
      AdviceTraceCertificate place available invariant []
  | step {available : List (AnyColumn × ℤ)} {invariant nextInvariant : ProverEnvironment F → Prop}
      {instruction : PlacedAdviceProgram F} {rest : List (PlacedAdviceProgram F)}
      (reads : AdviceProgramReadsFrom place available instruction.program)
      (frame : ∀ environment, invariant environment → ∀ address ∈ available,
        (runAdviceInstruction place instruction environment).get address.1 address.2 =
          environment.get address.1 address.2)
      (advance : ∀ environment, invariant environment →
        nextInvariant (runAdviceInstruction place instruction environment))
      (tail : AdviceTraceCertificate place (adviceProgramTarget instruction :: available) nextInvariant rest) :
      AdviceTraceCertificate place available invariant (instruction :: rest)

/-- A certified trace preserves all advice values available before the trace began. -/
theorem adviceTrace_preserves {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    {available : List (AnyColumn × ℤ)} {invariant : ProverEnvironment F → Prop}
    {programs : List (PlacedAdviceProgram F)}
    (certificate : AdviceTraceCertificate place available invariant programs)
    (environment : ProverEnvironment F) (hinvariant : invariant environment) :
    ∀ address ∈ available,
      (runAdvicePrograms place programs environment).get address.1 address.2 =
        environment.get address.1 address.2 := by
  induction certificate generalizing environment with
  | nil => intro address haddress; rfl
  | @step available invariant nextInvariant instruction rest reads frame advance tail ih =>
    intro address haddress
    exact (ih _ (advance environment hinvariant) address (List.mem_cons_of_mem _ haddress)).trans
      (frame environment hinvariant address haddress)

/-- A certified trace preserves the full read interface seen by earlier programs. -/
theorem adviceTrace_readAgreement {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    {available : List (AnyColumn × ℤ)} {invariant : ProverEnvironment F → Prop}
    {programs : List (PlacedAdviceProgram F)}
    (certificate : AdviceTraceCertificate place available invariant programs)
    (environment : ProverEnvironment F) (hinvariant : invariant environment) :
    AdviceReadAgreement available environment (runAdvicePrograms place programs environment) := by
  constructor
  · exact (runAdvicePrograms_hint place programs environment).symm
  · exact (runAdvicePrograms_usableRows place programs environment).symm
  · intro column row hkind
    exact (runAdvicePrograms_get_nonadvice place programs environment column row hkind).symm
  · intro address haddress
    exact (adviceTrace_preserves place certificate environment hinvariant address haddress).symm

/-- Every original advice equation holds after a certified trace, including repeated writes. -/
theorem adviceTrace_satisfies {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    {available : List (AnyColumn × ℤ)} {invariant : ProverEnvironment F → Prop}
    {programs : List (PlacedAdviceProgram F)}
    (certificate : AdviceTraceCertificate place available invariant programs)
    (environment : ProverEnvironment F) (hinvariant : invariant environment) :
    AdviceWitnessEquations place programs (runAdvicePrograms place programs environment) := by
  induction certificate generalizing environment with
  | nil => intro instruction hmem; cases hmem
  | @step available invariant nextInvariant instruction rest reads frame advance tail ih =>
    have hnext := advance environment hinvariant
    have hrest := ih _ hnext
    intro selected hselected
    rcases List.mem_cons.mp hselected with hselected | hselected
    · subst selected
      calc
        (runAdvicePrograms place (instruction :: rest) environment).get
            instruction.column.toAny (instruction.row : ℤ)
            = (runAdviceInstruction place instruction environment).get
                instruction.column.toAny (instruction.row : ℤ) :=
          adviceTrace_preserves place tail _ hnext _ List.mem_cons_self
        _ = (instruction.program.eval ⟨place, environment⟩)[0] :=
          writeAdviceValue_get_target _ _ _ _
        _ = (instruction.program.eval
            ⟨place, runAdvicePrograms place (instruction :: rest) environment⟩)[0] :=
          reads _ _ (adviceTrace_readAgreement place (.step reads frame advance tail) environment hinvariant)
    · exact hrest selected hselected

/-- A fresh target automatically preserves every earlier available cell. -/
theorem runAdviceInstruction_frame_of_fresh {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (instruction : PlacedAdviceProgram F)
    (available : List (AnyColumn × ℤ))
    (hfresh : adviceProgramTarget instruction ∉ available) (environment : ProverEnvironment F) :
    ∀ address ∈ available,
      (runAdviceInstruction place instruction environment).get address.1 address.2 =
        environment.get address.1 address.2 := by
  intro address haddress
  apply writeAdviceValue_get_frame
  intro heq
  have heqTarget : address = adviceProgramTarget instruction := Prod.ext heq.1 heq.2
  exact hfresh (by simpa only [heqTarget] using haddress)

/-- Writing a value already held by the target leaves the complete environment unchanged. -/
theorem runAdviceInstruction_eq_of_same_value {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (instruction : PlacedAdviceProgram F) (environment : ProverEnvironment F)
    (hvalue : (instruction.program.eval ⟨place, environment⟩)[0] =
      environment.get instruction.column.toAny (instruction.row : ℤ)) :
    runAdviceInstruction place instruction environment = environment := by
  apply proverEnvironment_ext
  · funext column row
    by_cases htarget : column = instruction.column.toAny ∧ row = (instruction.row : ℤ)
    · rcases htarget with ⟨rfl, rfl⟩
      exact (writeAdviceValue_get_target _ _ _ _).trans hvalue
    · exact writeAdviceValue_get_frame _ _ _ _ _ _ htarget
  · rfl
  · rfl

/-- A certified source trace and the compiler-owned fixed data establish full witness extension. -/
theorem topLevelAdviceAssignment_extendsWitnesses_of_trace
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (circuit : TopLevelCircuit Fp Config PublicInput) (initial : ProofAssignment Fp) (hints : ProverHint Fp)
    (invariant : ProverEnvironment Fp → Prop)
    (certificate : AdviceTraceCertificate circuit.placement [] invariant
      (circuitAdvicePrograms circuit.placement circuit.operations 0))
    (hinvariant : invariant (circuit.proverEnvironment initial hints)) :
    ExtendsWitnesses circuit.placement
      (circuit.proverEnvironment (topLevelAdviceAssignment circuit initial hints) hints)
      circuit.operations 0 := by
  rw [topLevelAdviceAssignment_environment]
  apply (circuitWitnessEquations_iff circuit.placement circuit.operations 0 _).mpr
  constructor
  · exact adviceTrace_satisfies circuit.placement certificate _ hinvariant
  · exact (runAdvicePrograms_fixedWitnesses circuit.placement _ _ circuit.operations 0).mpr
      (compiledEnvironment_fixedWitnesses circuit initial hints)

end Zcash.Snark.ZeroKnowledge
