import Zcash.Snark.ZeroKnowledge.PlonkColumnConstructorCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Complete lookup-prefix construction budget for one selected stored key entry. -/
def storedLookupSortCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare actions columns rowRead thetaRead : ℕ)
    (stored : StoredPlonkKey) (lookup : Fin 3) : ℕ :=
  let input := stored.lookupInputCosted read lookup
  let table := stored.lookupTableCosted read lookup
  input.2 + table.2 + lookupSortedPrefixesCostBudget canonicalRead compare equal 2042
    (plonkLookupCompressionCostBudget costs node equal read omegaAccess actions columns rowRead thetaRead 2042 input.1)
    (plonkLookupCompressionCostBudget costs node equal read omegaAccess actions columns rowRead thetaRead 2042 table.1) + 1

/-- A uniform preparation bound covers history reversal and any original lookup sort. -/
def plonkColumnPrepareCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare actions columns rowRead thetaRead : ℕ)
    (stored : StoredPlonkKey) : ℕ :=
  2 * columns + 3 + ∑ lookup : Fin 3,
    storedLookupSortCostBudget costs node equal read omegaAccess canonicalRead compare
      actions columns rowRead thetaRead stored lookup

/-- A uniform row-reader bound covers advice, stored sorted rows, and every original product computation. -/
def plonkColumnRowCostBudget (costs : FieldOperationCosts)
    (node equal read omegaAccess actions columns rowRead witnessRead thetaRead betaRead gammaRead : ℕ)
    (stored : StoredPlonkKey) : ℕ :=
  witnessRead + (4085 + read) +
    plonkPermutationProductCostBudget costs equal read omegaAccess actions columns rowRead betaRead gammaRead
      (read + 1) (stored.chunkLen, read + 1) (stored.layoutCosted read) +
    (∑ lookup : Fin 3, plonkLookupProductCostBudget costs node equal read omegaAccess actions columns rowRead
      thetaRead betaRead gammaRead (stored.lookupInputCosted read lookup) (stored.lookupTableCosted read lookup)) + 1

/-- Every column preparation retains the complete history and selected sorting work. -/
theorem plonkConstructColumnResultCosted_prepare_cost_le (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (Fin 2048 → Fp × ℕ)) (rowRead : ℕ)
    (hinstances : ∀ a r, (instances a r).2 ≤ rowRead) (hfixed : ∀ c r, (fixed c r).2 ≤ rowRead)
    (hrows : ∀ column ∈ history, ∀ r, (column r).2 ≤ rowRead) :
    (plonkConstructColumnResultCosted costs node equal read omegaAccess canonicalRead compare
      stored instances fixed sigma witness theta beta gamma id history).2 ≤
      plonkColumnPrepareCostBudget costs node equal read omegaAccess canonicalRead compare
        actions history.length rowRead theta.2 stored := by
  let budget := storedLookupSortCostBudget costs node equal read omegaAccess canonicalRead compare
    actions history.length rowRead theta.2 stored
  have hs (a : Fin actions) (l : Fin 3) :
      (plonkLookupSortedRowsCosted costs node equal read omegaAccess canonicalRead compare instances fixed
        history.reverse theta a (stored.lookupInputCosted read l) (stored.lookupTableCosted read l)).2 ≤ budget l := by
    simpa only [budget, storedLookupSortCostBudget, List.length_reverse] using
      plonkLookupSortedRowsCosted_cost_le costs node equal read omegaAccess canonicalRead compare
        instances fixed history.reverse theta a (stored.lookupInputCosted read l) (stored.lookupTableCosted read l)
        rowRead hinstances hfixed (fun column hc r => hrows column (List.mem_reverse.mp hc) r)
  have hb (l : Fin 3) : budget l ≤ ∑ i : Fin 3, budget i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  cases id with
  | advice a c => simp only [plonkConstructColumnResultCosted, plonkColumnPrepareCostBudget]; omega
  | lookupInput a l =>
      have h := (hs a l).trans (hb l)
      simp only [plonkConstructColumnResultCosted, reverseListCosted_result, reverseListCosted_cost]
      change _ ≤ 2 * history.length + 3 + ∑ i : Fin 3, budget i
      omega
  | lookupTable a l =>
      have h := (hs a l).trans (hb l)
      simp only [plonkConstructColumnResultCosted, reverseListCosted_result, reverseListCosted_cost]
      change _ ≤ 2 * history.length + 3 + ∑ i : Fin 3, budget i
      omega
  | permutationProduct a s =>
      simp only [plonkConstructColumnResultCosted, reverseListCosted_cost, plonkColumnPrepareCostBudget]
      omega
  | lookupProduct a l =>
      simp only [plonkConstructColumnResultCosted, reverseListCosted_cost, plonkColumnPrepareCostBudget]
      omega

end Zcash.Snark.ZeroKnowledge
