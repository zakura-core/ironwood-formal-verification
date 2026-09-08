import Zcash.Snark.ZeroKnowledge.AdviceWitnessTrace

/-!
# Copy aliases for repeated advice writes

An alias root names an already established cell or immutable input with the same
value. Fresh copies extend that relation. Copying between cells with the same
root leaves every value unchanged, which permits the shared base-point writes
without assuming that distinct circuit cells have distinct storage locations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- The absolute address used by the advice execution certificate. -/
abbrev AdviceAddress := AnyColumn × ℤ

/-- Unwritten cells are their own roots; established aliases point to stable inputs. -/
structure AdviceAliasesWellFormed (available : List AdviceAddress)
    (root : AdviceAddress → AdviceAddress) : Prop where
  unwritten : ∀ address, address ∉ available → root address = address
  stable : ∀ address ∈ available,
    root address ∈ available ∨ (root address).1.kind ≠ .advice

/-- Every recorded alias holds in the current prover environment. -/
def AdviceAliasValues {F : Type} (root : AdviceAddress → AdviceAddress)
    (environment : ProverEnvironment F) : Prop :=
  ∀ address, environment.get address.1 address.2 = environment.get (root address).1 (root address).2

/-- Initially every cell is its own root. -/
theorem adviceAliasesWellFormed_empty : AdviceAliasesWellFormed [] id := by
  constructor
  · intros; rfl
  · intro address hmem; cases hmem

/-- The identity root imposes no condition on the initial environment. -/
theorem adviceAliasValues_id {F : Type} (environment : ProverEnvironment F) :
    AdviceAliasValues id environment := by
  intro address
  rfl

/-- A stable root of another cell cannot be a fresh advice target. -/
theorem adviceAliasRoot_ne_fresh {available : List AdviceAddress}
    {root : AdviceAddress → AdviceAddress} (wellFormed : AdviceAliasesWellFormed available root)
    (target : AdviceAddress) (hkind : target.1.kind = .advice) (hfresh : target ∉ available)
    (address : AdviceAddress) (hne : address ≠ target) : root address ≠ target := by
  by_cases havailable : address ∈ available
  · rcases wellFormed.stable address havailable with hroot | hroot
    · intro heq
      exact hfresh (heq ▸ hroot)
    · intro heq
      exact hroot (heq ▸ hkind)
  · rw [wellFormed.unwritten address havailable]
    exact hne

/-- Adding an established cell without changing the roots preserves their structural invariant. -/
theorem adviceAliasesWellFormed_cons {available : List AdviceAddress}
    {root : AdviceAddress → AdviceAddress} (wellFormed : AdviceAliasesWellFormed available root)
    (target : AdviceAddress) : AdviceAliasesWellFormed (target :: available) root := by
  constructor
  · intro address hnot
    exact wellFormed.unwritten address (fun hmem => hnot (List.mem_cons_of_mem _ hmem))
  · intro address hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · subst address
      by_cases hold : target ∈ available
      · rcases wellFormed.stable target hold with hroot | hroot
        · exact Or.inl (List.mem_cons_of_mem _ hroot)
        · exact Or.inr hroot
      · exact Or.inl (by rw [wellFormed.unwritten target hold]; exact List.mem_cons_self)
    · rcases wellFormed.stable address hmem with hroot | hroot
      · exact Or.inl (List.mem_cons_of_mem _ hroot)
      · exact Or.inr hroot

/-- Copying an available or immutable source gives a stable root for the fresh target. -/
theorem adviceAliasesWellFormed_copy {available : List AdviceAddress}
    {root : AdviceAddress → AdviceAddress} (wellFormed : AdviceAliasesWellFormed available root)
    (target source : AdviceAddress)
    (hsource : source ∈ available ∨ source.1.kind ≠ .advice) :
    AdviceAliasesWellFormed (target :: available) (Function.update root target (root source)) := by
  constructor
  · intro address hnot
    have hne : address ≠ target := fun heq => hnot (heq ▸ List.mem_cons_self)
    rw [Function.update_of_ne hne]
    exact wellFormed.unwritten address (fun hmem => hnot (List.mem_cons_of_mem _ hmem))
  · intro address hmem
    by_cases heq : address = target
    · subst address
      rw [Function.update_self]
      by_cases havailable : source ∈ available
      · rcases wellFormed.stable source havailable with hroot | hroot
        · exact Or.inl (List.mem_cons_of_mem _ hroot)
        · exact Or.inr hroot
      · rw [wellFormed.unwritten source havailable]
        exact Or.inr (hsource.resolve_left havailable)
    · rw [Function.update_of_ne heq]
      exact (adviceAliasesWellFormed_cons wellFormed target).stable address hmem

/-- One instruction preserves every address other than its target. -/
theorem runAdviceInstruction_value_frame {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (instruction : PlacedAdviceProgram F)
    (environment : ProverEnvironment F) (address : AdviceAddress)
    (hne : address ≠ adviceProgramTarget instruction) :
    (runAdviceInstruction place instruction environment).get address.1 address.2 =
      environment.get address.1 address.2 := by
  apply writeAdviceValue_get_frame
  intro heq
  exact hne (Prod.ext heq.1 heq.2)

/-- A fresh arbitrary computation preserves all previously established copy aliases. -/
theorem adviceAliasValues_fresh {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (instruction : PlacedAdviceProgram F)
    {available : List AdviceAddress} {root : AdviceAddress → AdviceAddress}
    (wellFormed : AdviceAliasesWellFormed available root)
    (hfresh : adviceProgramTarget instruction ∉ available)
    (environment : ProverEnvironment F) (hvalues : AdviceAliasValues root environment) :
    AdviceAliasValues root (runAdviceInstruction place instruction environment) := by
  intro address
  by_cases htarget : address = adviceProgramTarget instruction
  · subst address
    rw [wellFormed.unwritten _ hfresh]
  · rw [runAdviceInstruction_value_frame place instruction environment address htarget,
      runAdviceInstruction_value_frame place instruction environment (root address)
        (adviceAliasRoot_ne_fresh wellFormed _ rfl hfresh address htarget)]
    exact hvalues address

/-- A source-read certificate describes the actual scalar program, including a native copy callback. -/
def AdviceCopySemantics {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (instruction : PlacedAdviceProgram F) (source : AdviceAddress) : Prop :=
  ∀ environment, (instruction.program.eval ⟨place, environment⟩)[0] =
    environment.get source.1 source.2

/-- A fresh copy establishes its new alias and preserves all old aliases. -/
theorem adviceAliasValues_copy_fresh {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (instruction : PlacedAdviceProgram F)
    {available : List AdviceAddress} {root : AdviceAddress → AdviceAddress}
    (wellFormed : AdviceAliasesWellFormed available root)
    (hfresh : adviceProgramTarget instruction ∉ available) (source : AdviceAddress)
    (hsource : source ∈ available ∨ source.1.kind ≠ .advice)
    (hcopy : AdviceCopySemantics place instruction source)
    (environment : ProverEnvironment F) (hvalues : AdviceAliasValues root environment) :
    AdviceAliasValues (Function.update root (adviceProgramTarget instruction) (root source))
      (runAdviceInstruction place instruction environment) := by
  have hsourceNe : source ≠ adviceProgramTarget instruction := by
    intro heq
    rcases hsource with havailable | hkind
    · exact hfresh (heq ▸ havailable)
    · exact hkind (heq ▸ rfl)
  have hrootNe := adviceAliasRoot_ne_fresh wellFormed _ rfl hfresh source hsourceNe
  intro address
  by_cases htarget : address = adviceProgramTarget instruction
  · subst address
    rw [Function.update_self]
    change (runAdviceInstruction place instruction environment).get instruction.column.toAny (instruction.row : ℤ) = _
    rw [runAdviceInstruction_value_frame place instruction environment (root source) hrootNe]
    exact (writeAdviceValue_get_target _ _ _ _).trans ((hcopy environment).trans (hvalues source))
  · rw [Function.update_of_ne htarget]
    rw [runAdviceInstruction_value_frame place instruction environment address htarget,
      runAdviceInstruction_value_frame place instruction environment (root address)
        (adviceAliasRoot_ne_fresh wellFormed _ rfl hfresh address htarget)]
    exact hvalues address

/-- Rewriting a cell from an equal-root source leaves the entire environment unchanged. -/
theorem adviceAliasCopy_eq_self {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (instruction : PlacedAdviceProgram F)
    (root : AdviceAddress → AdviceAddress) (source : AdviceAddress)
    (hcopy : AdviceCopySemantics place instruction source)
    (hsame : root (adviceProgramTarget instruction) = root source)
    (environment : ProverEnvironment F) (hvalues : AdviceAliasValues root environment) :
    runAdviceInstruction place instruction environment = environment := by
  apply runAdviceInstruction_eq_of_same_value
  rw [hcopy environment, hvalues source]
  exact (hsame ▸ hvalues (adviceProgramTarget instruction)).symm

end Zcash.Snark.ZeroKnowledge
