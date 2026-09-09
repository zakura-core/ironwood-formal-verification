import Zcash.Snark.ZeroKnowledge.WitnessBuilderSupport
import Clean.Halo2.Basic

/-!
# Semantic read support for native witness functions

Native callbacks are ordinary functions, so their dependencies cannot be inferred
by the structured IR collector. This predicate certifies the actual function:
equal immutable context data and equal listed cell values imply equal results.
It composes through arbitrary deterministic arithmetic on those results.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Witgen

/-- The declared cell reads and immutable context determine the actual callback result. -/
def WitnessFunctionSupport {F Value : Type} [FiniteField F]
    (reads : List (AssignedCell F)) (compute : Placed ProverEnvironment F → Value) : Prop :=
  ∀ left right, WitnessContextAgreement reads
    ({ env := left } : CtxOver F (Placed ProverEnvironment F)) { env := right } →
      compute left = compute right

/-- Enlarging the declared read set preserves a semantic support certificate. -/
theorem WitnessFunctionSupport.mono {F Value : Type} [FiniteField F]
    {reads larger : List (AssignedCell F)} {compute : Placed ProverEnvironment F → Value}
    (support : WitnessFunctionSupport reads compute) (hincluded : reads ⊆ larger) :
    WitnessFunctionSupport larger compute :=
  fun left right agreement => support left right (agreement.mono hincluded)

/-- A deterministic function of supported data introduces no additional environment read. -/
theorem WitnessFunctionSupport.map {F Value Result : Type} [FiniteField F]
    {reads : List (AssignedCell F)} {compute : Placed ProverEnvironment F → Value}
    (support : WitnessFunctionSupport reads compute) (f : Value → Result) :
    WitnessFunctionSupport reads (fun env => f (compute env)) :=
  fun left right agreement => congrArg f (support left right agreement)

/-- Pair two supported computations using the concatenation of their read sets. -/
theorem WitnessFunctionSupport.pair {F Left Right : Type} [FiniteField F]
    {leftReads rightReads : List (AssignedCell F)}
    {leftCompute : Placed ProverEnvironment F → Left} {rightCompute : Placed ProverEnvironment F → Right}
    (leftSupport : WitnessFunctionSupport leftReads leftCompute)
    (rightSupport : WitnessFunctionSupport rightReads rightCompute) :
    WitnessFunctionSupport (leftReads ++ rightReads) (fun env => (leftCompute env, rightCompute env)) :=
  fun left right agreement => Prod.ext
    (leftSupport left right agreement.left) (rightSupport left right agreement.right)

/-- A fixed value needs no cell read. -/
theorem witnessFunctionSupport_const {F Value : Type} [FiniteField F] (value : Value) :
    WitnessFunctionSupport (F := F) [] (fun _ => value) := fun _ _ _ => rfl

/-- Reading one assigned cell has exactly that cell as a sufficient support. -/
theorem witnessFunctionSupport_readCell {F : Type} [FiniteField F] (cell : AssignedCell F) :
    WitnessFunctionSupport [cell] (fun env => readCell env cell) :=
  fun _ _ agreement => agreement.cellValues cell (List.mem_singleton_self _)

/-- Structured field or record builders supply a support for native callers. -/
theorem witnessFunctionSupport_valueBuilder {F : Type} [FiniteField F]
    {value : TypeMap} [ProvableType value]
    (program : MOver F (AssignedCell F) (value (FExpr F))) :
    WitnessFunctionSupport (valueBuilderReads program) (fun env => program.eval env) :=
  fun left right agreement => valueBuilderReads_eval program left right agreement

/-- Native callers of a structured Nat builder inherit all its collected reads. -/
theorem witnessFunctionSupport_natBuilder {F : Type} [FiniteField F]
    (program : MOver F (AssignedCell F) (NExpr F)) :
    WitnessFunctionSupport (natBuilderReads program) (fun env => program.evalNat env) :=
  fun left right agreement => natBuilderReads_eval program left right agreement

/-- Native callers of a structured Boolean builder inherit all its collected reads. -/
theorem witnessFunctionSupport_boolBuilder {F : Type} [FiniteField F]
    (program : MOver F (AssignedCell F) (BExpr F)) :
    WitnessFunctionSupport (boolBuilderReads program) (fun env => program.evalBool env) :=
  fun left right agreement => boolBuilderReads_eval program left right agreement

/-- Semantic support plus availability proves the source-position read certificate. -/
theorem witnessFunctionSupport_readsFrom {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (available : List (AnyColumn × ℤ))
    (reads : List (AssignedCell F)) (program : WitgenIR F 1)
    (support : WitnessFunctionSupport reads (fun env => (program.eval env)[0]))
    (hreads : ∀ cell ∈ reads, cell.cell.column.kind = .advice →
      placedWitnessCell place cell ∈ available) :
    AdviceProgramReadsFrom place available program :=
  fun left right agreement => support ⟨place, left⟩ ⟨place, right⟩
    (adviceReadAgreement_context place available reads left right agreement hreads)

end Zcash.Snark.ZeroKnowledge
