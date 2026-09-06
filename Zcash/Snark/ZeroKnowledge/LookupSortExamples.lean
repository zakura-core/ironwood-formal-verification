import Zcash.Snark.ZeroKnowledge.LookupSort

/-!
# Deterministic checks of the specified lookup value order

These small prefixes exercise highest-row-first filling, duplicate table occurrences,
and a missing input value. The expected output lists follow the stated placement rule.
They are checked by kernel proofs using the general canonical-order theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Ascending unused values occupy the free rows in descending row order. -/
theorem lookupSort_reverse_fill_example : lookupSortColumns id [2, 2, 2, 5, 5] [1, 2, 3, 4, 5] =
    some ([2, 2, 2, 5, 5], [2, 4, 3, 5, 1]) := by
  have hb := canonicalLookupSort_eq_of_ordered id Function.injective_id [2, 2, 2, 5, 5] (by simp)
  have ht := canonicalLookupSort_eq_of_ordered id Function.injective_id [1, 2, 3, 4, 5] (by simp)
  simp [lookupSortColumns, hb, ht, lookupRunPlan, reserveLookupValues, fillLookupPlan]

/-- One duplicate table occurrence is reserved and the other remains available for filling. -/
theorem lookupSort_duplicate_table_example : lookupSortColumns id [1, 1, 3, 3] [1, 2, 3, 3] =
    some ([1, 1, 3, 3], [1, 3, 3, 2]) := by
  have hb := canonicalLookupSort_eq_of_ordered id Function.injective_id [1, 1, 3, 3] (by simp)
  have ht := canonicalLookupSort_eq_of_ordered id Function.injective_id [1, 2, 3, 3] (by simp)
  simp [lookupSortColumns, hb, ht, lookupRunPlan, reserveLookupValues, fillLookupPlan]

/-- An absent required value makes the construction fail. -/
theorem lookupSort_missing_value_example : lookupSortColumns id [2, 2] [1, 1] = none := by
  have hb := canonicalLookupSort_eq_of_ordered id Function.injective_id [2, 2] (by simp)
  have ht := canonicalLookupSort_eq_of_ordered id Function.injective_id [1, 1] (by simp)
  simp [lookupSortColumns, hb, ht, lookupRunPlan, reserveLookupValues, fillLookupPlan]

end Zcash.Snark.ZeroKnowledge
