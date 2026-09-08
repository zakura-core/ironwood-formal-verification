import Zcash.Snark.ZeroKnowledge.NativeCopyComposition
import Clean.Halo2.Loops

/-!
# Copy-source certificates through witness-program composition

Accumulator-dependent loops retain the native-source obligation for every actual
iteration. Scalar builders assemble structured IR and therefore create no native
copy-source obligation.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2

/-- Native source certificates compose through every accumulator-dependent iteration. -/
theorem regionNativeCopiesSound_foldRange {F β : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (source : NativeAdviceCopySource) (region : RegionIndex)
    (offset stride count : ℕ) (initial : β) (body : ℕ → ℕ → β → RegionCircuit F β)
    (hbody : ∀ index current accumulator,
      RegionNativeCopiesSound place source region ((body index current accumulator).operations region)) :
    RegionNativeCopiesSound place source region
      ((RegionCircuit.foldRange offset stride count initial body).operations region) := by
  rw [regionNativeCopiesSound_iff_operations, ← List.forall_iff_forall_mem,
    RegionCircuit.foldRange_forall]
  intro index
  rw [List.forall_iff_forall_mem, ← regionNativeCopiesSound_iff_operations]
  exact hbody _ _ _

/-- A scalar builder produces structured IR, regardless of its input expression. -/
theorem nativeCopyOperationSound_toIRScalar {F : Type} [FiniteField F]
    (place : RegionIndex → ℕ) (source : NativeAdviceCopySource) (region : RegionIndex)
    (column : Column .advice) (row : ℕ)
    (program : Witgen.MOver F (AssignedCell F) (FExpr F)) :
    NativeCopyOperationSound place source region
      (.assignAdvice column row program.toIRScalar) := by
  rw [Witgen.MOver.toIRScalar_def]
  simp only [Witgen.MOver.toIR, NativeCopyOperationSound]

end Zcash.Snark.ZeroKnowledge
