import Zcash.Snark.ZeroKnowledge.AdviceAliasCollection

/-!
# Composing native copy-source certificates

Only native advice assignments can create an obligation. The lemmas expose this
operation-level predicate and preserve it across the source list's concatenation
boundaries, so gadget proofs can reuse the original subcircuit operations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- The native source obligation of one original region operation. -/
def NativeCopyOperationSound {F : Type} [FiniteField F] (place : RegionIndex → ℕ)
    (nativeSource : NativeAdviceCopySource) (region : RegionIndex) : RegionOperation F → Prop
  | .assignAdvice column row (.native callback) =>
    ∀ source, nativeSource region column row = some source →
      AdviceCopySemantics place ⟨column, place region + row, .native callback⟩ source
  | _ => True

/-- The region certificate is exactly the native obligation at every original operation. -/
theorem regionNativeCopiesSound_iff_operations {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (nativeSource : NativeAdviceCopySource)
    (region : RegionIndex) (programs : RegionOperations F) :
    RegionNativeCopiesSound place nativeSource region programs ↔
      ∀ operation ∈ programs, NativeCopyOperationSound place nativeSource region operation := by
  constructor
  · intro hnative operation hmem
    cases operation with
    | assignAdvice column row program =>
      cases program with
      | native callback => exact hnative column row callback hmem
      | ir steps output => trivial
    | _ => trivial
  · intro hnative column row callback hmem
    exact hnative _ hmem

/-- Native obligations split exactly across the original operation-list concatenation. -/
theorem regionNativeCopiesSound_append {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (nativeSource : NativeAdviceCopySource)
    (region : RegionIndex) (left right : RegionOperations F) :
    RegionNativeCopiesSound place nativeSource region (left ++ right) ↔
      RegionNativeCopiesSound place nativeSource region left ∧
        RegionNativeCopiesSound place nativeSource region right := by
  simp only [regionNativeCopiesSound_iff_operations, List.mem_append, or_imp, forall_and]

/-- Native obligations split into the current source operation and the remaining source list. -/
theorem regionNativeCopiesSound_cons {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (nativeSource : NativeAdviceCopySource)
    (region : RegionIndex) (operation : RegionOperation F) (rest : RegionOperations F) :
    RegionNativeCopiesSound place nativeSource region (operation :: rest) ↔
      NativeCopyOperationSound place nativeSource region operation ∧
        RegionNativeCopiesSound place nativeSource region rest := by
  simp only [regionNativeCopiesSound_iff_operations, List.forall_mem_cons]

/-- An empty source list imposes no native obligations. -/
theorem regionNativeCopiesSound_nil {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (nativeSource : NativeAdviceCopySource) (region : RegionIndex) :
    RegionNativeCopiesSound (F := F) place nativeSource region [] := by
  intro column row callback hmem
  cases hmem

/-- Disabling native annotations at a region discharges its native-source predicate for any operations. -/
theorem regionNativeCopiesSound_of_none {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (nativeSource : NativeAdviceCopySource)
    (region : RegionIndex) (programs : RegionOperations F)
    (hnone : ∀ column row, nativeSource region column row = none) :
    RegionNativeCopiesSound place nativeSource region programs := by
  intro column row callback _ source hsource
  rw [hnone column row] at hsource
  cases hsource

end Zcash.Snark.ZeroKnowledge
