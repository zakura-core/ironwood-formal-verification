import Zcash.Snark.ZeroKnowledge.AdviceAliasInvariant

/-!
# Checking advice writes through copy aliases

The Boolean checker accepts a repeated target only when the actual program is
certified as a copy and its source has the same established root. The soundness
proof builds the full trace certificate. Read dependencies and the source
certificates concern the original programs; they are not inferred from a tag.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Check fresh writes and equal-root copies while threading the established alias roots. -/
def adviceAliasPlan {F : Type} : List AdviceAddress → (AdviceAddress → AdviceAddress) →
    List (PlacedAdviceProgram F × Option AdviceAddress) → Bool
  | _, _, [] => true
  | available, root, (instruction, none) :: rest =>
    if adviceProgramTarget instruction ∈ available then false
    else adviceAliasPlan (adviceProgramTarget instruction :: available) root rest
  | available, root, (instruction, some source) :: rest =>
    if source ∈ available ∨ source.1.kind ≠ .advice then
      if adviceProgramTarget instruction ∈ available then
        if root (adviceProgramTarget instruction) = root source then
          adviceAliasPlan (adviceProgramTarget instruction :: available) root rest
        else false
      else adviceAliasPlan (adviceProgramTarget instruction :: available)
        (Function.update root (adviceProgramTarget instruction) (root source)) rest
    else false

/-- Every copy tag must describe the actual program's value in every environment. -/
def AdviceAliasSources {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (PlacedAdviceProgram F × Option AdviceAddress)) : Prop :=
  ∀ instruction source, (instruction, some source) ∈ programs →
    AdviceCopySemantics place instruction source

/-- Successful alias checking constructs a value-preserving trace from the program certificates. -/
theorem adviceAliasPlan_certificate {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (programs : List (PlacedAdviceProgram F × Option AdviceAddress))
    {available : List AdviceAddress} {root : AdviceAddress → AdviceAddress}
    (hcheck : adviceAliasPlan available root programs = true)
    (hreads : AdviceProgramsCausal place available (programs.map Prod.fst))
    (hsources : AdviceAliasSources place programs)
    (wellFormed : AdviceAliasesWellFormed available root) :
    AdviceTraceCertificate place available (AdviceAliasValues root) (programs.map Prod.fst) := by
  induction programs generalizing available root with
  | nil => exact .nil _ _
  | cons entry rest ih =>
    rcases entry with ⟨instruction, source⟩
    obtain ⟨hread, hreadsTail⟩ := hreads
    have hsourcesTail : AdviceAliasSources place rest := by
      intro selected source hmem
      exact hsources selected source (List.mem_cons_of_mem _ hmem)
    cases source with
    | none =>
      by_cases hknown : adviceProgramTarget instruction ∈ available
      · simp only [adviceAliasPlan, if_pos hknown, Bool.false_eq_true] at hcheck
      · simp only [adviceAliasPlan, if_neg hknown] at hcheck
        apply AdviceTraceCertificate.step hread
        · intro environment _
          exact runAdviceInstruction_frame_of_fresh place instruction available hknown environment
        · intro environment hvalues
          exact adviceAliasValues_fresh place instruction wellFormed hknown environment hvalues
        · exact ih hcheck hreadsTail hsourcesTail (adviceAliasesWellFormed_cons wellFormed _)
    | some source =>
      have hcopy := hsources instruction source List.mem_cons_self
      by_cases hsource : source ∈ available ∨ source.1.kind ≠ .advice
      · simp only [adviceAliasPlan, if_pos hsource] at hcheck
        by_cases hknown : adviceProgramTarget instruction ∈ available
        · simp only [if_pos hknown] at hcheck
          by_cases hsame : root (adviceProgramTarget instruction) = root source
          · simp only [if_pos hsame] at hcheck
            apply AdviceTraceCertificate.step hread
            · intro environment hvalues address _
              rw [adviceAliasCopy_eq_self place instruction root source hcopy hsame environment hvalues]
            · intro environment hvalues
              rw [adviceAliasCopy_eq_self place instruction root source hcopy hsame environment hvalues]
              exact hvalues
            · exact ih hcheck hreadsTail hsourcesTail (adviceAliasesWellFormed_cons wellFormed _)
          · simp only [if_neg hsame, Bool.false_eq_true] at hcheck
        · simp only [if_neg hknown] at hcheck
          apply AdviceTraceCertificate.step hread
          · intro environment _
            exact runAdviceInstruction_frame_of_fresh place instruction available hknown environment
          · intro environment hvalues
            exact adviceAliasValues_copy_fresh place instruction wellFormed hknown source hsource hcopy environment hvalues
          · exact ih hcheck hreadsTail hsourcesTail (adviceAliasesWellFormed_copy wellFormed _ source hsource)
      · simp only [adviceAliasPlan, if_neg hsource, Bool.false_eq_true] at hcheck

/-- The checked alias plan and actual program certificates establish compiler-level witness extension. -/
theorem topLevelAdviceAssignment_extendsWitnesses_of_aliasPlan
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (circuit : TopLevelCircuit Fp Config PublicInput) (initial : ProofAssignment Fp) (hints : ProverHint Fp)
    (programs : List (PlacedAdviceProgram Fp × Option AdviceAddress))
    (hprograms : programs.map Prod.fst = circuitAdvicePrograms circuit.placement circuit.operations 0)
    (hcheck : adviceAliasPlan [] id programs = true)
    (hreads : AdviceProgramsCausal circuit.placement [] (programs.map Prod.fst))
    (hsources : AdviceAliasSources circuit.placement programs) :
    ExtendsWitnesses circuit.placement
      (circuit.proverEnvironment (topLevelAdviceAssignment circuit initial hints) hints)
      circuit.operations 0 := by
  have htrace := adviceAliasPlan_certificate circuit.placement programs hcheck hreads hsources adviceAliasesWellFormed_empty
  rw [hprograms] at htrace
  exact topLevelAdviceAssignment_extendsWitnesses_of_trace circuit initial hints
    (AdviceAliasValues id) htrace (adviceAliasValues_id _)

end Zcash.Snark.ZeroKnowledge
