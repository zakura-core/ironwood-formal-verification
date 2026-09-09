import Zcash.Snark.ZeroKnowledge.AdviceAliasAddressPlan
import Std.Data.TreeMap.Lemmas

/-!
# A finite map representing the alias checker's state

The map stores established root labels at injectively encoded addresses. Its
lookup laws identify both availability and the original total root function.
This keeps later numerical checks independent of a growing linear membership
list while retaining the original alias policy.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2

attribute [local instance] lexOrd

/-- A comparison key retaining the column kind, column index, and signed row. -/
def adviceAddressKey (address : AdviceAddress) : ℕ × ℕ × ℤ :=
  ((match address.1.kind with | .advice => 0 | .fixed => 1 | .instance => 2),
    address.1.index, address.2)

/-- The finite-map key never identifies distinct cell addresses. -/
theorem adviceAddressKey_injective : Function.Injective adviceAddressKey := by
  rintro ⟨⟨leftKind, leftColumn⟩, leftRow⟩ ⟨⟨rightKind, rightColumn⟩, rightRow⟩
  cases leftKind <;> cases rightKind <;> simp [adviceAddressKey]

/-- Established roots indexed by the complete cell address. -/
abbrev AdviceAliasMap := Std.TreeMap (ℕ × ℕ × ℤ) AdviceAddress

/-- Read a root label only when that address has been established. -/
def adviceAliasMapLookup (roots : AdviceAliasMap) (address : AdviceAddress) : Option AdviceAddress :=
  roots[adviceAddressKey address]?

/-- Install one established root label. -/
def adviceAliasMapInsert (roots : AdviceAliasMap) (address root : AdviceAddress) : AdviceAliasMap :=
  roots.insert (adviceAddressKey address) root

/-- An empty map establishes no address. -/
theorem adviceAliasMapLookup_empty (address : AdviceAddress) :
    adviceAliasMapLookup ∅ address = none := by
  simp [adviceAliasMapLookup]

/-- Insertion changes precisely its selected address, including across column kinds. -/
theorem adviceAliasMapLookup_insert (roots : AdviceAliasMap) (target value address : AdviceAddress) :
    adviceAliasMapLookup (adviceAliasMapInsert roots target value) address =
      if target = address then some value else adviceAliasMapLookup roots address := by
  simp [adviceAliasMapLookup, adviceAliasMapInsert, Std.TreeMap.getElem?_insert,
    adviceAddressKey_injective.eq_iff]

/-- Exact representation of the original list and total root function. -/
structure AdviceAliasMapRepresents (roots : AdviceAliasMap) (available : List AdviceAddress)
    (root : AdviceAddress → AdviceAddress) : Prop where
  lookup : ∀ address, adviceAliasMapLookup roots address =
    if address ∈ available then some (root address) else none
  unassigned : ∀ address, address ∉ available → root address = address

/-- The initial finite map represents the original empty checker state. -/
theorem adviceAliasMapRepresents_empty : AdviceAliasMapRepresents ∅ [] id := by
  constructor
  · intro address
    simp [adviceAliasMapLookup_empty]
  · intro address _
    rfl

/-- Falling back to an unassigned address recovers the original total root function. -/
theorem AdviceAliasMapRepresents.root {roots : AdviceAliasMap} {available : List AdviceAddress}
    {root : AdviceAddress → AdviceAddress} (represents : AdviceAliasMapRepresents roots available root)
    (address : AdviceAddress) : (adviceAliasMapLookup roots address).getD address = root address := by
  rw [represents.lookup]
  by_cases h : address ∈ available
  · simp [h]
  · simp [h, represents.unassigned address h]

/-- Finite-map presence is exactly the original availability predicate. -/
theorem AdviceAliasMapRepresents.known {roots : AdviceAliasMap} {available : List AdviceAddress}
    {root : AdviceAddress → AdviceAddress} (represents : AdviceAliasMapRepresents roots available root)
    (address : AdviceAddress) :
    (adviceAliasMapLookup roots address).isSome = decide (address ∈ available) := by
  rw [represents.lookup]
  split <;> simp_all

/-- Insertion represents the same single-address update as the original root function. -/
theorem AdviceAliasMapRepresents.insert {roots : AdviceAliasMap} {available : List AdviceAddress}
    {root : AdviceAddress → AdviceAddress} (represents : AdviceAliasMapRepresents roots available root)
    (target value : AdviceAddress) :
    AdviceAliasMapRepresents (adviceAliasMapInsert roots target value) (target :: available)
      (Function.update root target value) := by
  constructor
  · intro address
    rw [adviceAliasMapLookup_insert]
    by_cases h : target = address
    · subst address
      simp
    · rw [if_neg h, represents.lookup]
      simp [Ne.symm h, Function.update_of_ne]
  · intro address h
    have htarget : address ≠ target := by
      intro heq
      exact h (by simp [heq])
    rw [Function.update_of_ne htarget]
    exact represents.unassigned address (fun hmem => h (List.mem_cons_of_mem _ hmem))

/-- A fresh ordinary write stores its own unchanged root. -/
theorem AdviceAliasMapRepresents.insert_self {roots : AdviceAliasMap} {available : List AdviceAddress}
    {root : AdviceAddress → AdviceAddress} (represents : AdviceAliasMapRepresents roots available root)
    (target : AdviceAddress) (hfresh : target ∉ available) :
    AdviceAliasMapRepresents (adviceAliasMapInsert roots target target) (target :: available) root := by
  have h := represents.insert target (root target)
  rw [Function.update_eq_self] at h
  simpa only [represents.unassigned target hfresh] using h

/-- A repeated target adds no new map entry and does not alter existing roots. -/
theorem AdviceAliasMapRepresents.cons_known {roots : AdviceAliasMap} {available : List AdviceAddress}
    {root : AdviceAddress → AdviceAddress} (represents : AdviceAliasMapRepresents roots available root)
    (target : AdviceAddress) (hknown : target ∈ available) :
    AdviceAliasMapRepresents roots (target :: available) root := by
  constructor
  · intro address
    rw [represents.lookup]
    by_cases h : address = target
    · subst address
      simp [hknown]
    · simp [h]
  · intro address h
    exact represents.unassigned address (fun hmem => h (List.mem_cons_of_mem _ hmem))

end Zcash.Snark.ZeroKnowledge
