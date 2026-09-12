import Zcash.Snark.ZeroKnowledge.WitnessProgramSupport

/-!
# Read support of witness builders

Native gadget callbacks often receive a structured scalar or point builder as
an input. These results retain the builder's local steps and output reads, so a
native callback's certificate can include the actual nested hint computation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen

/-- Complete variable support of a structured field-valued or record-valued builder. -/
def valueBuilderReads {F V : Type} {value : TypeMap} [ProvableType value]
    (program : MOver F V (value (FExprOver F V))) : List V :=
  stepsWitnessReads (program #[]).2.toList ++ listWitnessReads (toElements (program #[]).1).toList

/-- Complete variable support of a Nat-valued builder, including its local steps. -/
def natBuilderReads {F V : Type} (program : MOver F V (NExprOver F V)) : List V :=
  stepsWitnessReads (program #[]).2.toList ++ natWitnessReads (program #[]).1

/-- Complete variable support of a Boolean-valued builder, including its local steps. -/
def boolBuilderReads {F V : Type} (program : MOver F V (BExprOver F V)) : List V :=
  stepsWitnessReads (program #[]).2.toList ++ boolWitnessReads (program #[]).1

variable {F Env V : Type} [FiniteField F] [WitgenEnv F Env V]

/-- The actual value-builder evaluator depends only on its declared variable support. -/
theorem valueBuilderReads_eval {value : TypeMap} [ProvableType value]
    (program : MOver F V (value (FExprOver F V))) (left right : Env)
    (agreement : WitnessContextAgreement (valueBuilderReads program)
      ({ env := left } : CtxOver F Env) { env := right }) :
    program.eval left = program.eval right := by
  have hvalues : (program.toIRLiteral (Env := Env)).eval left =
      (program.toIRLiteral (Env := Env)).eval right :=
    structuredWitnessReads_eval (program #[]).2.toList (.lit (toElements (program #[]).1)) left right agreement
  rw [MOver.eval_toIRLiteral, MOver.eval_toIRLiteral] at hvalues
  simpa only [ProvableType.fromElements_toElements] using
    congrArg (fromElements (M := value)) hvalues

/-- The actual Nat-builder evaluator depends only on its declared variable support. -/
theorem natBuilderReads_eval (program : MOver F V (NExprOver F V)) (left right : Env)
    (agreement : WitnessContextAgreement (natBuilderReads program)
      ({ env := left } : CtxOver F Env) { env := right }) :
    program.evalNat left = program.evalNat right := by
  have hsteps := stepsWitnessReads_eval (program #[]).2.toList _ _ agreement.left
  simp only [MOver.evalNat]
  rw [hsteps]
  exact natWitnessReads_eval (program #[]).1 _ _
    (agreement.right.withLocals (evalSteps right (program #[]).2.toList))

/-- The actual Boolean-builder evaluator depends only on its declared variable support. -/
theorem boolBuilderReads_eval (program : MOver F V (BExprOver F V)) (left right : Env)
    (agreement : WitnessContextAgreement (boolBuilderReads program)
      ({ env := left } : CtxOver F Env) { env := right }) :
    program.evalBool left = program.evalBool right := by
  have hsteps := stepsWitnessReads_eval (program #[]).2.toList _ _ agreement.left
  simp only [MOver.evalBool]
  rw [hsteps]
  exact boolWitnessReads_eval (program #[]).1 _ _
    (agreement.right.withLocals (evalSteps right (program #[]).2.toList))

/-- The scalar program emitted by a builder has exactly that builder's read support. -/
theorem scalarBuilder_readsFrom {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (available : List (AnyColumn × ℤ))
    (program : MOver F (AssignedCell F) (FExpr F))
    (hreads : ∀ cell ∈ valueBuilderReads (value := field) program,
      cell.cell.column.kind = .advice → placedWitnessCell place cell ∈ available) :
    AdviceProgramReadsFrom place available (program.toIRScalar (Env := Placed ProverEnvironment F)) := by
  intro left right agreement
  rw [MOver.eval_toIRScalar, MOver.eval_toIRScalar]
  exact valueBuilderReads_eval (value := field) program (⟨place, left⟩ : Placed ProverEnvironment F) ⟨place, right⟩
    (adviceReadAgreement_context place available _ left right agreement hreads)

end Zcash.Snark.ZeroKnowledge
