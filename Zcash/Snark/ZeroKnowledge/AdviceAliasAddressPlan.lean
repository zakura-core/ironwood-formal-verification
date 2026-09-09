import Zcash.Snark.ZeroKnowledge.AdviceAliasCollection

/-!
# The address data used by the alias checker

The finite check depends only on write addresses and certified copy addresses.
These projections discard witness function bodies while preserving exactly the
existing alias policy. The source collectors below retain the original operation
and region order; their equalities are proved for arbitrary programs.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

/-- The complete address data consulted by the original alias checker. -/
def adviceAliasAddressData {F : Type}
    (programs : List (PlacedAdviceProgram F × Option AdviceAddress)) :
    List (AdviceAddress × Option AdviceAddress) :=
  programs.map (fun entry => (adviceProgramTarget entry.1, entry.2))

/-- The same alias policy acting only on its finite address data. -/
def adviceAddressAliasPlan : List AdviceAddress → (AdviceAddress → AdviceAddress) →
    List (AdviceAddress × Option AdviceAddress) → Bool
  | _, _, [] => true
  | available, root, (target, none) :: rest =>
    if target ∈ available then false
    else adviceAddressAliasPlan (target :: available) root rest
  | available, root, (target, some source) :: rest =>
    if source ∈ available ∨ source.1.kind ≠ .advice then
      if target ∈ available then
        if root target = root source then
          adviceAddressAliasPlan (target :: available) root rest
        else false
      else adviceAddressAliasPlan (target :: available)
        (Function.update root target (root source)) rest
    else false

/-- Discarding witness bodies preserves the original check exactly, including rejection. -/
theorem adviceAliasPlan_eq_addressPlan {F : Type}
    (programs : List (PlacedAdviceProgram F × Option AdviceAddress))
    (available : List AdviceAddress) (root : AdviceAddress → AdviceAddress) :
    adviceAliasPlan available root programs =
      adviceAddressAliasPlan available root (adviceAliasAddressData programs) := by
  induction programs generalizing available root with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨instruction, source⟩
    cases source <;>
      simp [adviceAliasPlan, adviceAddressAliasPlan, adviceAliasAddressData, ih]

/-- Extract only the address data from each original region operation. -/
def regionAdviceAliasAddresses {F : Type} (place : RegionIndex → ℕ) (region : RegionIndex)
    (nativeSource : NativeAdviceCopySource) : RegionOperations F →
      List (AdviceAddress × Option AdviceAddress)
  | [] => []
  | .assignAdvice column row program :: rest =>
    let source := match program with
      | .native _ => nativeSource region column row
      | .ir _ _ => witnessCopyAddress place program
    ((column.toAny, (place region + row : ℕ)), source) ::
      regionAdviceAliasAddresses place region nativeSource rest
  | _ :: rest => regionAdviceAliasAddresses place region nativeSource rest

/-- Extract the same data with the original circuit's region-index threading. -/
def circuitAdviceAliasAddresses {F : Type} (place : RegionIndex → ℕ)
    (nativeSource : NativeAdviceCopySource) :
    Operations F → RegionIndex → List (AdviceAddress × Option AdviceAddress)
  | [], _ => []
  | .region _ body :: rest, region =>
    regionAdviceAliasAddresses place region nativeSource body ++
      circuitAdviceAliasAddresses place nativeSource rest (region + 1)
  | _ :: rest, region => circuitAdviceAliasAddresses place nativeSource rest region

/-- The reduced region collector is exactly the projection of the original annotated programs. -/
theorem regionAdviceAliasAddresses_eq {F : Type} (place : RegionIndex → ℕ) (region : RegionIndex)
    (nativeSource : NativeAdviceCopySource) (operations : RegionOperations F) :
    adviceAliasAddressData (regionAdviceAliases place region nativeSource operations) =
      regionAdviceAliasAddresses place region nativeSource operations := by
  induction operations with
  | nil => rfl
  | cons operation rest ih =>
    simp only [adviceAliasAddressData, adviceProgramTarget] at ih
    cases operation with
    | assignAdvice column row program =>
      cases program <;>
        simp [adviceAliasAddressData, regionAdviceAliases, regionAdviceAliasAddresses,
          adviceProgramTarget, ih]
    | _ => exact ih

/-- The reduced circuit collector retains every target, copy tag, and original source position. -/
theorem circuitAdviceAliasAddresses_eq {F : Type} (place : RegionIndex → ℕ)
    (nativeSource : NativeAdviceCopySource) (operations : Operations F) (region : RegionIndex) :
    adviceAliasAddressData (circuitAdviceAliases place nativeSource operations region) =
      circuitAdviceAliasAddresses place nativeSource operations region := by
  induction operations generalizing region with
  | nil => rfl
  | cons operation rest ih =>
    simp only [adviceAliasAddressData] at ih ⊢
    cases operation <;>
      simp only [circuitAdviceAliases, circuitAdviceAliasAddresses, List.map_append]
    all_goals first
      | exact ih _
      | exact congrArg₂ List.append (regionAdviceAliasAddresses_eq _ _ _ _) (ih _)

end Zcash.Snark.ZeroKnowledge
