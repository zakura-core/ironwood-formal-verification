import Zcash.Snark.ZeroKnowledge.AdviceAliasMap

/-!
# Checking alias addresses with a finite root map

This implementation uses the proved map representation instead of rescanning the
complete preceding address list. The refinement preserves every Boolean result
of the original checker, including all rejection branches.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- Check fresh writes and equal-root copies using the finite root map. -/
def adviceAliasMapPlan : AdviceAliasMap → List (AdviceAddress × Option AdviceAddress) → Bool
  | _, [] => true
  | roots, (target, none) :: rest =>
    match adviceAliasMapLookup roots target with
    | some _ => false
    | none => adviceAliasMapPlan (adviceAliasMapInsert roots target target) rest
  | roots, (target, some source) :: rest =>
    if (adviceAliasMapLookup roots source).isSome = true ∨ source.1.kind ≠ .advice then
      let sourceRoot := (adviceAliasMapLookup roots source).getD source
      match adviceAliasMapLookup roots target with
      | some targetRoot =>
        if targetRoot = sourceRoot then adviceAliasMapPlan roots rest else false
      | none => adviceAliasMapPlan (adviceAliasMapInsert roots target sourceRoot) rest
    else false

/-- A represented state gives exactly the same result as the original address policy. -/
theorem adviceAliasMapPlan_eq (entries : List (AdviceAddress × Option AdviceAddress))
    (roots : AdviceAliasMap) (available : List AdviceAddress) (root : AdviceAddress → AdviceAddress)
    (represents : AdviceAliasMapRepresents roots available root) :
    adviceAliasMapPlan roots entries = adviceAddressAliasPlan available root entries := by
  induction entries generalizing roots available root with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨target, source⟩
    cases source with
    | none =>
      simp only [adviceAliasMapPlan, adviceAddressAliasPlan, represents.lookup]
      by_cases htarget : target ∈ available
      · simp [htarget]
      · simp only [if_neg htarget]
        exact ih _ _ _ (represents.insert_self target htarget)
    | some source =>
      simp only [adviceAliasMapPlan, adviceAddressAliasPlan, represents.known,
        decide_eq_true_eq, represents.root]
      by_cases hsource : source ∈ available ∨ source.1.kind ≠ .advice
      · simp only [if_pos hsource, represents.lookup]
        by_cases htarget : target ∈ available
        · simp only [if_pos htarget]
          by_cases hroot : root target = root source
          · simp only [if_pos hroot]
            exact ih _ _ _ (represents.cons_known target htarget)
          · simp [hroot]
        · simp only [if_neg htarget]
          exact ih _ _ _ (represents.insert target (root source))
      · simp [hsource]

/-- The finite-map implementation preserves the original witness-program check exactly. -/
theorem adviceAliasMapPlan_original {F : Type}
    (programs : List (PlacedAdviceProgram F × Option AdviceAddress)) :
    adviceAliasMapPlan ∅ (adviceAliasAddressData programs) = adviceAliasPlan [] id programs := by
  rw [adviceAliasMapPlan_eq _ _ _ _ adviceAliasMapRepresents_empty]
  exact (adviceAliasPlan_eq_addressPlan programs [] id).symm

/-- The fused source collector and map checker preserve the complete original circuit check. -/
theorem circuitAdviceAliasMapPlan_original {F : Type} (place : RegionIndex → ℕ)
    (nativeSource : NativeAdviceCopySource) (operations : Operations F) (region : RegionIndex) :
    adviceAliasMapPlan ∅ (circuitAdviceAliasAddresses place nativeSource operations region) =
      adviceAliasPlan [] id (circuitAdviceAliases place nativeSource operations region) := by
  rw [← circuitAdviceAliasAddresses_eq]
  exact adviceAliasMapPlan_original _

end Zcash.Snark.ZeroKnowledge
