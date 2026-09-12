import Zcash.Snark.ZeroKnowledge.AdviceAliasPlan
import Zcash.Snark.ZeroKnowledge.WitnessCopySemantics

/-!
# Collecting copy annotations without changing witness execution

Structured copy sources are recognized from the original IR. A supplied native
annotation is accepted semantically only with a proof about the corresponding
source operation. Erasing all annotations recovers the exact existing program
list, in source order and at the same placement.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Optional native-copy addresses indexed by original region, column, and local row. -/
abbrev NativeAdviceCopySource := RegionIndex → Column .advice → ℕ → Option AdviceAddress

/-- Collect the original region programs together with structured or supplied native copy sources. -/
def regionAdviceAliases {F : Type} (place : RegionIndex → ℕ) (region : RegionIndex)
    (nativeSource : NativeAdviceCopySource) : RegionOperations F →
      List (PlacedAdviceProgram F × Option AdviceAddress)
  | [] => []
  | .assignAdvice column row program :: rest =>
    let instruction := (⟨column, place region + row, program⟩ : PlacedAdviceProgram F)
    let source := match program with
      | .native _ => nativeSource region column row
      | .ir _ _ => witnessCopyAddress place program
    (instruction, source) :: regionAdviceAliases place region nativeSource rest
  | _ :: rest => regionAdviceAliases place region nativeSource rest

/-- Collect annotations while preserving the source circuit's region-index threading. -/
def circuitAdviceAliases {F : Type} (place : RegionIndex → ℕ) (nativeSource : NativeAdviceCopySource) :
    Operations F → RegionIndex → List (PlacedAdviceProgram F × Option AdviceAddress)
  | [], _ => []
  | .region _ body :: rest, region =>
    regionAdviceAliases place region nativeSource body ++
      circuitAdviceAliases place nativeSource rest (region + 1)
  | _ :: rest, region => circuitAdviceAliases place nativeSource rest region

/-- Erasing region annotations gives exactly the original placed advice programs. -/
theorem regionAdviceAliases_erase {F : Type} (place : RegionIndex → ℕ) (region : RegionIndex)
    (nativeSource : NativeAdviceCopySource) (programs : RegionOperations F) :
    (regionAdviceAliases place region nativeSource programs).map Prod.fst =
      regionAdvicePrograms place region programs := by
  induction programs with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;> simp [regionAdviceAliases, regionAdvicePrograms, ih]

/-- Erasing circuit annotations gives exactly the original source-order execution list. -/
theorem circuitAdviceAliases_erase {F : Type} (place : RegionIndex → ℕ)
    (nativeSource : NativeAdviceCopySource) (programs : Operations F) (region : RegionIndex) :
    (circuitAdviceAliases place nativeSource programs region).map Prod.fst =
      circuitAdvicePrograms place programs region := by
  induction programs generalizing region with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;>
      simp [circuitAdviceAliases, circuitAdvicePrograms, List.map_append, regionAdviceAliases_erase, ih]

/-- Native tags must be justified for every matching original operation in a region. -/
def RegionNativeCopiesSound {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (nativeSource : NativeAdviceCopySource) (region : RegionIndex) (programs : RegionOperations F) : Prop :=
  ∀ column row callback, RegionOperation.assignAdvice column row (.native callback) ∈ programs →
    ∀ source, nativeSource region column row = some source →
      AdviceCopySemantics place ⟨column, place region + row, .native callback⟩ source

/-- The source circuit's native-copy obligations, with unchanged region indexing. -/
def CircuitNativeCopiesSound {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (nativeSource : NativeAdviceCopySource) : Operations F → RegionIndex → Prop
  | [], _ => True
  | .region _ body :: rest, region =>
    RegionNativeCopiesSound place nativeSource region body ∧
      CircuitNativeCopiesSound place nativeSource rest (region + 1)
  | _ :: rest, region => CircuitNativeCopiesSound place nativeSource rest region

/-- Sound native annotations and the checked IR recognizer justify all collected region copy sources. -/
theorem regionAdviceAliases_sources {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (region : RegionIndex) (nativeSource : NativeAdviceCopySource) (programs : RegionOperations F)
    (hnative : RegionNativeCopiesSound place nativeSource region programs) :
    AdviceAliasSources place (regionAdviceAliases place region nativeSource programs) := by
  induction programs with
  | nil => intro instruction source hmem; cases hmem
  | cons operation rest ih =>
    have hrest : RegionNativeCopiesSound place nativeSource region rest := by
      intro column row callback hmem source hsource
      exact hnative column row callback (List.mem_cons_of_mem _ hmem) source hsource
    cases operation with
    | assignAdvice column row program =>
      intro selected source hmem
      rcases List.mem_cons.mp hmem with heq | htail
      · cases program with
        | native callback =>
          have hselected := congrArg Prod.fst heq
          have hsource := congrArg Prod.snd heq
          dsimp only at hselected hsource
          subst selected
          exact hnative column row callback List.mem_cons_self source hsource.symm
        | ir steps output =>
          have hselected := congrArg Prod.fst heq
          have hsource := congrArg Prod.snd heq
          dsimp only at hselected hsource
          subst selected
          exact witnessCopyAddress_semantics place _ source hsource.symm
      · exact ih hrest selected source htail
    | _ => exact ih hrest

/-- Sound native annotations justify every copy source in the original complete circuit. -/
theorem circuitAdviceAliases_sources {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (nativeSource : NativeAdviceCopySource) (programs : Operations F) (region : RegionIndex)
    (hnative : CircuitNativeCopiesSound place nativeSource programs region) :
    AdviceAliasSources place (circuitAdviceAliases place nativeSource programs region) := by
  induction programs generalizing region with
  | nil => intro instruction source hmem; cases hmem
  | cons operation rest ih =>
    cases operation with
    | region name body =>
      intro instruction source hmem
      rcases List.mem_append.mp hmem with hbody | htail
      · exact regionAdviceAliases_sources place region nativeSource body hnative.1 instruction source hbody
      · exact ih (region + 1) hnative.2 instruction source htail
    | _ => exact ih region hnative

end Zcash.Snark.ZeroKnowledge
