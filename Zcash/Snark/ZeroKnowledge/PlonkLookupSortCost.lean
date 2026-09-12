import Zcash.Snark.ZeroKnowledge.PlonkLookupCompressionCostBound
import Zcash.Snark.ZeroKnowledge.LookupSortRowsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Construct the real lookup prefixes from their original stored expression trees and rows. -/
def plonkLookupSortedRowsCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta : Fp × ℕ) (action : Fin actions)
    (inputExprs tableExprs : List (Expr Fp) × ℕ) : Option (List Fp × List Fp) × ℕ :=
  let sorted := lookupSortedPrefixesCosted canonicalRead compare equal 2042
    (plonkLookupCompressedRowsCosted costs node equal read omegaAccess
      instances fixed rows theta action inputExprs.1)
    (plonkLookupCompressedRowsCosted costs node equal read omegaAccess
      instances fixed rows theta action tableExprs.1)
  (sorted.1, inputExprs.2 + tableExprs.2 + sorted.2 + 1)

/-- The counted sort equals the complete original row constructor, including failure. -/
theorem plonkLookupSortedRowsCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta : Fp × ℕ) (action : Fin actions) (lookup : Fin 3)
    (inputRead tableRead : ℕ) :
    (plonkLookupSortedRowsCosted costs node equal read omegaAccess canonicalRead compare
      instances fixed rows theta action (vk.lookupInputExprs lookup, inputRead)
        (vk.lookupTableExprs lookup, tableRead)).1 =
      plonkLookupSortedRows vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1) (fun c r => (fixed c r).1) sigma)
        (rows.map (fun column r => (column r).1)) theta.1 action lookup := by
  simp only [plonkLookupSortedRowsCosted, lookupSortedPrefixesCosted_result,
    plonkLookupCompressedRowsCosted_result costs node equal read omegaAccess instances fixed sigma,
    plonkLookupSortedRows]

/-- The complete prefix bound discharges both row-reader budgets from their counted computations. -/
theorem plonkLookupSortedRowsCosted_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ}
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ)
    (rows : List (Fin 2048 → Fp × ℕ)) (theta : Fp × ℕ) (action : Fin actions)
    (inputExprs tableExprs : List (Expr Fp) × ℕ) (rowRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead)
    (hrows : ∀ column ∈ rows, ∀ r, (column r).2 ≤ rowRead) :
    (plonkLookupSortedRowsCosted costs node equal read omegaAccess canonicalRead compare
      instances fixed rows theta action inputExprs tableExprs).2 ≤
      inputExprs.2 + tableExprs.2 + lookupSortedPrefixesCostBudget canonicalRead compare equal 2042
        (plonkLookupCompressionCostBudget costs node equal read omegaAccess actions rows.length
          rowRead theta.2 2042 inputExprs.1)
        (plonkLookupCompressionCostBudget costs node equal read omegaAccess actions rows.length
          rowRead theta.2 2042 tableExprs.1) + 1 := by
  have h := lookupSortedPrefixesCosted_cost_le canonicalRead compare equal 2042
    (plonkLookupCompressedRowsCosted costs node equal read omegaAccess instances fixed rows theta action inputExprs.1)
    (plonkLookupCompressedRowsCosted costs node equal read omegaAccess instances fixed rows theta action tableExprs.1)
    _ _ (fun i hi => plonkLookupCompressedRowsCosted_cost_le costs node equal read omegaAccess
      instances fixed rows theta action inputExprs.1 i 2042 rowRead (Nat.le_of_lt hi) hinstances hfixed hrows)
    (fun i hi => plonkLookupCompressedRowsCosted_cost_le costs node equal read omegaAccess
      instances fixed rows theta action tableExprs.1 i 2042 rowRead (Nat.le_of_lt hi) hinstances hfixed hrows)
  exact Nat.add_le_add_right (Nat.add_le_add_left h (inputExprs.2 + tableExprs.2)) 1

end Zcash.Snark.ZeroKnowledge
