import Zcash.Snark.ZeroKnowledge.PlonkLookupSortCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Successful real lookup construction materializes exactly the two usable prefixes. -/
theorem plonkLookupSortedRowsCosted_lengths (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ) (fixed : Fin 29 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta : Fp × ℕ) (action : Fin actions)
    (input table : List (Expr Fp) × ℕ) (output : List Fp × List Fp)
    (h : (plonkLookupSortedRowsCosted costs node equal read omegaAccess canonicalRead compare
      instances fixed rows theta action input table).1 = some output) :
    output.1.length = 2042 ∧ output.2.length = 2042 := by
  simp only [plonkLookupSortedRowsCosted, lookupSortedPrefixesCosted_result] at h
  have result := lookupSortedPrefixes_correct 2042 _ _ output.1 output.2 h
  exact ⟨result.1, result.2.1⟩

/-- Reading either stored output keeps its traversal cost, including zero defaults after the prefix. -/
theorem plonkLookupSortedRowsCosted_read_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ) (fixed : Fin 29 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta : Fp × ℕ) (action : Fin actions)
    (input table : List (Expr Fp) × ℕ) (output : List Fp × List Fp)
    (h : (plonkLookupSortedRowsCosted costs node equal read omegaAccess canonicalRead compare
      instances fixed rows theta action input table).1 = some output) (index : ℕ) :
    (getDListCosted read 0 output.1 index).2 ≤ 4085 + read ∧
      (getDListCosted read 0 output.2 index).2 ≤ 4085 + read := by
  have hl := plonkLookupSortedRowsCosted_lengths costs node equal read omegaAccess canonicalRead compare
    instances fixed rows theta action input table output h
  have hi := getDListCosted_cost_le read (0 : Fp) output.1 index
  have ht := getDListCosted_cost_le read (0 : Fp) output.2 index
  rw [hl.1] at hi
  rw [hl.2] at ht
  constructor <;> omega

end Zcash.Snark.ZeroKnowledge
