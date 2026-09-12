import Zcash.Snark.ZeroKnowledge.StoredRowsCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimQueriesCost

/-!
# Materialized verifier expressions and permutation layout

The supplied key stores its expression trees and column layout directly. Lookup
families are lists, so selecting a lookup pays for the list traversal. Returning
a stored list reference does not traverse its contents; the existing expression
and permutation evaluators charge those later traversals in full.

The encoding is a representation of an already supplied key, not an algorithm
that generates the key or its commitments.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Stored algebraic key data consumed by the reference simulator. -/
structure StoredPlonkKey where
  omega : Fp
  n : ℕ
  blindingFactors : ℕ
  delta : Fp
  chunkLen : ℕ
  gates : List (Expr Fp)
  permutationChunks : List (List (ColumnRef × ℕ))
  lookupInputs : List (List (Expr Fp))
  lookupTables : List (List (Expr Fp))

/-- Materialize the original verifier key's three lookup families in index order. -/
def StoredPlonkKey.encode {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) : StoredPlonkKey where
  omega := vk.omega
  n := vk.n
  blindingFactors := vk.blindingFactors
  delta := vk.delta
  chunkLen := vk.chunkLen
  gates := vk.gates
  permutationChunks := vk.permutationChunks
  lookupInputs := List.ofFn vk.lookupInputExprs
  lookupTables := List.ofFn vk.lookupTableExprs

/-- Retrieve the stored gate-list reference; evaluating the trees is charged separately. -/
def StoredPlonkKey.gatesCosted (stored : StoredPlonkKey) (read : ℕ) : List (Expr Fp) × ℕ :=
  (stored.gates, read + 1)

/-- Retrieve the stored column-layout reference with its input access charge. -/
def StoredPlonkKey.layoutCosted (stored : StoredPlonkKey) (read : ℕ) :
    List (List (ColumnRef × ℕ)) × ℕ :=
  (stored.permutationChunks, read + 1)

/-- Select a stored lookup input, preserving the empty-list default. -/
def StoredPlonkKey.lookupInputCosted (stored : StoredPlonkKey) (read : ℕ) (index : Fin 3) :
    List (Expr Fp) × ℕ :=
  getDListCosted read [] stored.lookupInputs index.val

/-- Select a stored lookup table, preserving the empty-list default. -/
def StoredPlonkKey.lookupTableCosted (stored : StoredPlonkKey) (read : ℕ) (index : Fin 3) :
    List (Expr Fp) × ℕ :=
  getDListCosted read [] stored.lookupTables index.val

/-- The stored gate reader returns precisely the original key trees. -/
theorem StoredPlonkKey.gatesCosted_encode_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (read : ℕ) :
    ((StoredPlonkKey.encode vk).gatesCosted read).1 = vk.gates := rfl

/-- The stored layout reader returns precisely the original ordered column chunks. -/
theorem StoredPlonkKey.layoutCosted_encode_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (read : ℕ) :
    ((StoredPlonkKey.encode vk).layoutCosted read).1 = vk.permutationChunks := rfl

/-- Each stored lookup input agrees with the original finite key family. -/
theorem StoredPlonkKey.lookupInputCosted_encode_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (read : ℕ) (index : Fin 3) :
    ((StoredPlonkKey.encode vk).lookupInputCosted read index).1 = vk.lookupInputExprs index := by
  have hi : index.val < (List.ofFn vk.lookupInputExprs).length := by
    simpa only [List.length_ofFn] using index.isLt
  simp only [lookupInputCosted, encode, getDListCosted_result,
    List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  rfl

/-- Each stored lookup table agrees with the original finite key family. -/
theorem StoredPlonkKey.lookupTableCosted_encode_result {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (read : ℕ) (index : Fin 3) :
    ((StoredPlonkKey.encode vk).lookupTableCosted read index).1 = vk.lookupTableExprs index := by
  have hi : index.val < (List.ofFn vk.lookupTableExprs).length := by
    simpa only [List.length_ofFn] using index.isLt
  simp only [lookupTableCosted, encode, getDListCosted_result,
    List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  rfl

/-- The stored gate reference has its specified primitive read cost. -/
theorem StoredPlonkKey.gatesCosted_cost (stored : StoredPlonkKey) (read : ℕ) :
    (stored.gatesCosted read).2 = read + 1 := rfl

/-- The stored layout reference has its specified primitive read cost. -/
theorem StoredPlonkKey.layoutCosted_cost (stored : StoredPlonkKey) (read : ℕ) :
    (stored.layoutCosted read).2 = read + 1 := rfl

/-- Lookup-input access follows from the actual stored family length. -/
theorem StoredPlonkKey.lookupInputCosted_cost_le (stored : StoredPlonkKey) (read : ℕ)
    (index : Fin 3) :
    (stored.lookupInputCosted read index).2 ≤ 2 * stored.lookupInputs.length + read + 1 :=
  getDListCosted_cost_le read [] stored.lookupInputs index.val

/-- Lookup-table access follows from the actual stored family length. -/
theorem StoredPlonkKey.lookupTableCosted_cost_le (stored : StoredPlonkKey) (read : ℕ)
    (index : Fin 3) :
    (stored.lookupTableCosted read index).2 ≤ 2 * stored.lookupTables.length + read + 1 :=
  getDListCosted_cost_le read [] stored.lookupTables index.val

/-- Encoding a reference key gives a fixed three-entry lookup-input access bound. -/
theorem StoredPlonkKey.lookupInputCosted_encode_cost_le {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (read : ℕ) (index : Fin 3) :
    ((StoredPlonkKey.encode vk).lookupInputCosted read index).2 ≤ read + 7 := by
  have h := lookupInputCosted_cost_le (StoredPlonkKey.encode vk) read index
  simp only [encode, List.length_ofFn] at h
  change ((StoredPlonkKey.encode vk).lookupInputCosted read index).2 ≤ 2 * 3 + read + 1 at h
  omega

/-- Encoding a reference key gives a fixed three-entry lookup-table access bound. -/
theorem StoredPlonkKey.lookupTableCosted_encode_cost_le {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (read : ℕ) (index : Fin 3) :
    ((StoredPlonkKey.encode vk).lookupTableCosted read index).2 ≤ read + 7 := by
  have h := lookupTableCosted_cost_le (StoredPlonkKey.encode vk) read index
  simp only [encode, List.length_ofFn] at h
  change ((StoredPlonkKey.encode vk).lookupTableCosted read index).2 ≤ 2 * 3 + read + 1 at h
  omega

end Zcash.Snark.ZeroKnowledge
