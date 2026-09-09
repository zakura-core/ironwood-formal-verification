import Zcash.Snark.ZeroKnowledge.LookupSortCostBound
import Zcash.Snark.ZeroKnowledge.LookupSortRows

/-!
# Complete counted lookup-prefix construction

The original field sort uses the canonical `Fp.val` key. Its representation read,
integer comparison, and field equality have explicit primitive prices. Both
usable input vectors are fully materialized and their supplied row-reader costs
are retained before the complete sorting and table-fill pipeline is executed.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Read both complete usable prefixes and execute the original field-order sorter. -/
def lookupSortedPrefixesCosted (canonicalRead compare equal usable : ℕ)
    (input table : ℕ → Fp × ℕ) : Option (List Fp × List Fp) × ℕ :=
  let inputs := ofFnCosted fun index : Fin usable =>
    let value := input index.val
    (value.1, value.2 + 1)
  let tables := ofFnCosted fun index : Fin usable =>
    let value := table index.val
    (value.1, value.2 + 1)
  let sorted := lookupSortColumnsCosted (fun value : Fp => (value.val, canonicalRead + 1))
    compare equal inputs.1 tables.1
  (sorted.1, inputs.2 + tables.2 + sorted.2 + 2)

/-- Exact equality with the specified prefix sorter, including every failure case. -/
theorem lookupSortedPrefixesCosted_result (canonicalRead compare equal usable : ℕ)
    (input table : ℕ → Fp × ℕ) :
    (lookupSortedPrefixesCosted canonicalRead compare equal usable input table).1 =
      lookupSortedPrefixes usable (fun index => (input index).1) (fun index => (table index).1) := by
  simp only [lookupSortedPrefixesCosted, ofFnCosted_result]
  rw [lookupSortColumnsCosted_result (fun value : Fp => (value.val, canonicalRead + 1))
    compare equal _ _ (ZMod.val_injective Zcash.Arithmetic.scalarFieldOrder)]
  rfl

/-- The full prefix budget includes row preparation, both lists, sorting, and failures. -/
def lookupSortedPrefixesCostBudget (canonicalRead compare equal usable inputRead tableRead : ℕ) : ℕ :=
  lookupSortColumnsCostBudget compare equal (canonicalRead + 1) usable usable +
    usable * (inputRead + tableRead + 4) + 2 * usable ^ 2 + 4

/-- Complete polynomial cost of the original lookup-prefix result under priced row readers. -/
theorem lookupSortedPrefixesCosted_cost_le (canonicalRead compare equal usable : ℕ)
    (input table : ℕ → Fp × ℕ) (inputRead tableRead : ℕ)
    (hinput : ∀ index < usable, (input index).2 ≤ inputRead)
    (htable : ∀ index < usable, (table index).2 ≤ tableRead) :
    (lookupSortedPrefixesCosted canonicalRead compare equal usable input table).2 ≤
      lookupSortedPrefixesCostBudget canonicalRead compare equal usable inputRead tableRead := by
  let inputs := ofFnCosted fun index : Fin usable => ((input index.val).1, (input index.val).2 + 1)
  let tables := ofFnCosted fun index : Fin usable => ((table index.val).1, (table index.val).2 + 1)
  have hi : inputs.2 ≤ usable * (inputRead + 2) + usable * usable + 1 :=
    ofFnCosted_cost_le _ (inputRead + 1)
      (fun index => Nat.add_le_add_right (hinput index.val index.isLt) 1)
  have ht : tables.2 ≤ usable * (tableRead + 2) + usable * usable + 1 :=
    ofFnCosted_cost_le _ (tableRead + 1)
      (fun index => Nat.add_le_add_right (htable index.val index.isLt) 1)
  have hsort := lookupSortColumnsCosted_cost_le
    (fun value : Fp => (value.val, canonicalRead + 1)) compare equal inputs.1 tables.1
    (canonicalRead + 1) (fun _ => le_rfl)
  have hilen : inputs.1.length = usable := ofFnCosted_length _
  have htlen : tables.1.length = usable := ofFnCosted_length _
  rw [hilen, htlen] at hsort
  change inputs.2 + tables.2 +
    (lookupSortColumnsCosted (fun value : Fp => (value.val, canonicalRead + 1))
      compare equal inputs.1 tables.1).2 + 2 ≤ _
  unfold lookupSortedPrefixesCostBudget
  nlinarith

end Zcash.Snark.ZeroKnowledge
