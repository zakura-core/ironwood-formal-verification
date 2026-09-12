import Zcash.Snark.ZeroKnowledge.WitnessReadSupport

/-!
# Read support of complete structured witness programs

Local steps, vector outputs, and loop indices preserve the expression-level
dependency guarantee. Specializing it to placed Halo2 environments gives the
read certificate consumed by the advice interpreter. A native closure is never
accepted by the structured-program theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen

/-- Replacing both local stores by the same values preserves context agreement. -/
theorem WitnessContextAgreement.withLocals {F Env V : Type} [WitgenEnv F Env V]
    {reads : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement reads left right) (locals : Array (F ⊕ ℕ)) :
    WitnessContextAgreement reads { left with locals } { right with locals } :=
  { agreement with locals := rfl }

/-- Giving both vector loops the same iteration index preserves context agreement. -/
theorem WitnessContextAgreement.withIndex {F Env V : Type} [WitgenEnv F Env V]
    {reads : List V} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement reads left right) (index : ℕ) :
    WitnessContextAgreement reads { left with idx := index } { right with idx := index } :=
  { agreement with index := rfl }

/-- A list's complete support contains the support of every expression it can select. -/
theorem WitnessContextAgreement.list_member {F Env V : Type} [WitgenEnv F Env V]
    {expressions : List (FExprOver F V)} {left right : CtxOver F Env}
    (agreement : WitnessContextAgreement (listWitnessReads expressions) left right)
    {expression : FExprOver F V} (hmem : expression ∈ expressions) :
    WitnessContextAgreement (fieldWitnessReads expression) left right := by
  induction expressions with
  | nil => cases hmem
  | cons first rest ih =>
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact agreement.left
    · exact ih agreement.right hrest

/-- All cell atoms in a vector-shaped witness output. -/
def vectorWitnessReads {F V : Type} : {width : ℕ} → VExprOver F V width → List V
  | _, .lit expressions => listWitnessReads expressions.toList
  | _, .mapRange _ body => fieldWitnessReads body
  | _, .append left right => vectorWitnessReads left ++ vectorWitnessReads right

/-- All cell atoms read by the local steps of a structured witness program. -/
def stepsWitnessReads {F V : Type} : List (StepOver F V) → List V
  | [] => []
  | .letF expression :: rest => fieldWitnessReads expression ++ stepsWitnessReads rest
  | .letN expression :: rest => natWitnessReads expression ++ stepsWitnessReads rest

variable {F Env V : Type} [FiniteField F] [WitgenEnv F Env V]

/-- Vector evaluation introduces no variable reads beyond its collected support. -/
theorem vectorWitnessReads_eval {width : ℕ} (expression : VExprOver F V width)
    (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (vectorWitnessReads expression) left right) :
    expression.eval left = expression.eval right := by
  induction expression with
  | lit expressions =>
    ext index hindex
    simp only [VExprOver.eval, Vector.getElem_map]
    apply fieldWitnessReads_eval
    apply agreement.list_member
    exact List.getElem_mem (l := expressions.toList) (n := index) (by simpa using hindex)
  | mapRange width body =>
    ext index hindex
    simp only [VExprOver.eval, Vector.getElem_mapRange]
    exact fieldWitnessReads_eval body _ _ (agreement.withIndex index)
  | append first second ihfirst ihsecond =>
    simp only [VExprOver.eval, ihfirst agreement.left, ihsecond agreement.right]

/-- Sequential local evaluation depends only on the collected reads and initial local values. -/
theorem stepsWitnessReads_eval (steps : List (StepOver F V)) (left right : CtxOver F Env)
    (agreement : WitnessContextAgreement (stepsWitnessReads steps) left right) :
    evalSteps left.env steps left.locals = evalSteps right.env steps right.locals := by
  induction steps generalizing left right with
  | nil => exact agreement.locals
  | cons step rest ih =>
    cases step with
    | letF expression =>
      simp only [evalSteps]
      have hvalue := fieldWitnessReads_eval expression
        { env := left.env, locals := left.locals } { env := right.env, locals := right.locals }
        (agreement.left.withIndex 0)
      rw [hvalue, agreement.locals]
      exact ih _ _ (agreement.right.withLocals
        (right.locals.push (.inl (expression.eval { env := right.env, locals := right.locals }))))
    | letN expression =>
      simp only [evalSteps]
      have hvalue := natWitnessReads_eval expression
        { env := left.env, locals := left.locals } { env := right.env, locals := right.locals }
        (agreement.left.withIndex 0)
      rw [hvalue, agreement.locals]
      exact ih _ _ (agreement.right.withLocals
        (right.locals.push (.inr (expression.eval { env := right.env, locals := right.locals }))))

/-- The actual straight-line IR evaluator depends only on the complete declared variable support. -/
theorem structuredWitnessReads_eval {width : ℕ} (steps : List (StepOver F V))
    (output : VExprOver F V width) (left right : Env)
    (agreement : WitnessContextAgreement (stepsWitnessReads steps ++ vectorWitnessReads output)
      ({ env := left } : CtxOver F Env) { env := right }) :
    (WitgenIROver.ir steps output).eval left = (WitgenIROver.ir steps output).eval right := by
  have hsteps := stepsWitnessReads_eval steps _ _ agreement.left
  simp only [WitgenIROver.eval]
  rw [hsteps]
  exact vectorWitnessReads_eval output _ _ (agreement.right.withLocals (evalSteps right steps))

/-- The absolute address of a cell atom in the circuit's own placement. -/
def placedWitnessCell {F : Type} (place : RegionIndex → ℕ) (cell : AssignedCell F) : AnyColumn × ℤ :=
  (cell.cell.column, (place cell.cell.regionIndex + cell.cell.rowOffset : ℕ))

/-- Available advice and immutable inputs supply the structured evaluator's exact context contract. -/
theorem adviceReadAgreement_context {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (available : List (AnyColumn × ℤ)) (reads : List (AssignedCell F))
    (left right : ProverEnvironment F) (agreement : AdviceReadAgreement available left right)
    (hreads : ∀ cell ∈ reads, cell.cell.column.kind = .advice → placedWitnessCell place cell ∈ available) :
    WitnessContextAgreement reads
      ({ env := ⟨place, left⟩ } : CtxOver F (Placed ProverEnvironment F)) { env := ⟨place, right⟩ } := by
  constructor
  · intro cell hcell
    by_cases hadvice : cell.cell.column.kind = .advice
    · exact agreement.advice _ (hreads cell hcell hadvice)
    · exact agreement.nonAdvice _ _ hadvice
  · rfl
  · rfl
  · exact agreement.hints
  · rfl
  · rfl

/-- A support inclusion proves the actual structured program's advice-read certificate. -/
theorem structuredWitness_readsFrom {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (available : List (AnyColumn × ℤ))
    (steps : List (StepOver F (AssignedCell F))) (output : VExprOver F (AssignedCell F) 1)
    (hreads : ∀ cell ∈ stepsWitnessReads steps ++ vectorWitnessReads output,
      cell.cell.column.kind = .advice → placedWitnessCell place cell ∈ available) :
    AdviceProgramReadsFrom place available (.ir steps output) := by
  intro left right agreement
  exact congrArg (fun values : Vector F 1 => values[0])
    (structuredWitnessReads_eval steps output (⟨place, left⟩ : Placed ProverEnvironment F) ⟨place, right⟩
      (adviceReadAgreement_context place available _ left right agreement hreads))

end Zcash.Snark.ZeroKnowledge
