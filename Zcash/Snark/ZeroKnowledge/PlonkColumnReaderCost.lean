import Zcash.Snark.ZeroKnowledge.PlonkColumnCostBudget
import Zcash.Snark.ZeroKnowledge.PlonkLookupStoredRowsCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Every prepared row reader retains the complete computation selected by the original dispatcher. -/
theorem plonkConstructColumnResultCosted_row_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (Fin 2048 → Fp × ℕ)) (rowRead witnessRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead)
    (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead) (hsigma : ∀ c r, (sigma c r).2 ≤ rowRead)
    (hwitness : ∀ a c r, (witness a c r).2 ≤ witnessRead)
    (hrows : ∀ column ∈ history, ∀ r, (column r).2 ≤ rowRead)
    (column : Fin 2048 → Fp × ℕ)
    (hcolumn : (plonkConstructColumnResultCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma id history).1 = some column) (row : Fin 2048) :
    (column row).2 ≤ plonkColumnRowCostBudget costs node equal read omegaAccess actions history.length rowRead
      witnessRead theta.2 beta.2 gamma.2 stored := by
  let budget := plonkColumnRowCostBudget costs node equal read omegaAccess actions history.length rowRead
    witnessRead theta.2 beta.2 gamma.2 stored
  have ha : witnessRead ≤ budget := by dsimp only [budget, plonkColumnRowCostBudget]; omega
  have hs : 4085 + read ≤ budget := by dsimp only [budget, plonkColumnRowCostBudget]; omega
  have hp : plonkPermutationProductCostBudget costs equal read omegaAccess actions history.length rowRead
      beta.2 gamma.2 (read + 1) (stored.chunkLen, read + 1) (stored.layoutCosted read) ≤ budget := by
    dsimp only [budget, plonkColumnRowCostBudget]
    omega
  have hl (l : Fin 3) : plonkLookupProductCostBudget costs node equal read omegaAccess actions history.length
      rowRead theta.2 beta.2 gamma.2 (stored.lookupInputCosted read l) (stored.lookupTableCosted read l) ≤ budget := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun l : Fin 3 => plonkLookupProductCostBudget costs node equal read omegaAccess actions history.length
        rowRead theta.2 beta.2 gamma.2 (stored.lookupInputCosted read l) (stored.lookupTableCosted read l))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    dsimp only at h
    dsimp only [budget, plonkColumnRowCostBudget]
    omega
  have hr (values : Fin 2048 → Fp × ℕ) (hv : values ∈ history.reverse) (i : Fin 2048) :
      (values i).2 ≤ rowRead := hrows values (List.mem_reverse.mp hv) i
  change (column row).2 ≤ budget
  cases id with
  | advice a c =>
      simp only [plonkConstructColumnResultCosted, Option.some.injEq] at hcolumn
      rw [← hcolumn]
      exact (hwitness a c row).trans ha
  | lookupInput a l =>
      simp only [plonkConstructColumnResultCosted, reverseListCosted_result] at hcolumn
      obtain ⟨output, hsort, rfl⟩ := Option.map_eq_some_iff.mp hcolumn
      exact (plonkLookupSortedRowsCosted_read_cost_le costs node equal read omegaAccess canonicalRead compare
        instances fixed history.reverse theta a (stored.lookupInputCosted read l) (stored.lookupTableCosted read l)
        output hsort row.val).1.trans hs
  | lookupTable a l =>
      simp only [plonkConstructColumnResultCosted, reverseListCosted_result] at hcolumn
      obtain ⟨output, hsort, rfl⟩ := Option.map_eq_some_iff.mp hcolumn
      exact (plonkLookupSortedRowsCosted_read_cost_le costs node equal read omegaAccess canonicalRead compare
        instances fixed history.reverse theta a (stored.lookupInputCosted read l) (stored.lookupTableCosted read l)
        output hsort row.val).2.trans hs
  | permutationProduct a s =>
      simp only [plonkConstructColumnResultCosted, reverseListCosted_result, Option.some.injEq] at hcolumn
      rw [← hcolumn]
      have h := plonkPermutationBaseRowsCosted_cost_le costs equal read omegaAccess
        instances fixed sigma history.reverse beta gamma (stored.delta, read + 1)
        (stored.chunkLen, read + 1) (stored.layoutCosted read) a s row rowRead hinstances hfixed hsigma hr
      rw [List.length_reverse] at h
      exact h.trans hp
  | lookupProduct a l =>
      simp only [plonkConstructColumnResultCosted, reverseListCosted_result, Option.some.injEq] at hcolumn
      rw [← hcolumn]
      have h := plonkLookupBaseRowsCosted_cost_le costs node equal read omegaAccess
        instances fixed history.reverse theta beta gamma a l (stored.lookupInputCosted read l)
        (stored.lookupTableCosted read l) row rowRead hinstances hfixed hr
      rw [List.length_reverse] at h
      exact h.trans (hl l)

end Zcash.Snark.ZeroKnowledge
