import Zcash.Snark.ZeroKnowledge.LookupSortSuccess
import Zcash.Snark.ZeroKnowledge.LookupRowConstraints
import Zcash.Arithmetic.Field

/-!
# The specified lookup sorter supplies the verifier's row premises

The field-specific adapter sorts the usable prefixes by `Fp.val`, their canonical
integer order. Valid prefix membership guarantees success. A successful result
supplies both permutation laws and the first-row/run-structure facts consumed by
the existing row-constraint theorem.

The masked-column schedule must still establish the expression feeds, retained scan
rows, and rotations. This file does not assume uniform prover randomness.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Compute the usable permuted lookup prefixes in canonical field order. -/
def lookupSortedPrefixes (usable : ℕ) (input table : ℕ → Fp) : Option (List Fp × List Fp) :=
  lookupSortColumns (fun value : Fp => value.val)
    (List.ofFn fun i : Fin usable => input i.val) (List.ofFn fun i : Fin usable => table i.val)

/-- Valid scalar lookup membership makes the prefix construction succeed. -/
theorem lookupSortedPrefixes_exists (usable : ℕ) (input table : ℕ → Fp)
    (hmember : ∀ i < usable, ∃ j, j < usable ∧ input i = table j) :
    ∃ output, lookupSortedPrefixes usable input table = some output := by
  apply lookupSortColumns_exists (fun value : Fp => value.val)
    (ZMod.val_injective Zcash.Arithmetic.scalarFieldOrder)
  · simp
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, hj, heq⟩ := hmember i.val i.isLt
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, heq.symm⟩

/-- The computed prefixes supply every sorting fact needed by the row constraints. -/
theorem lookupSortedPrefixes_correct (usable : ℕ) (input table : ℕ → Fp) (b t : List Fp)
    (hsort : lookupSortedPrefixes usable input table = some (b, t)) :
    b.length = usable ∧ t.length = usable ∧
    (List.ofFn fun i : Fin usable => input i.val).Perm
      (List.ofFn fun i : Fin usable => b.getD i.val 0) ∧
    (List.ofFn fun i : Fin usable => table i.val).Perm
      (List.ofFn fun i : Fin usable => t.getD i.val 0) ∧
    b.getD 0 0 = t.getD 0 0 ∧
    ∀ i, 0 < i → i < usable → b.getD i 0 = t.getD i 0 ∨ b.getD i 0 = b.getD (i - 1) 0 := by
  obtain ⟨hinput, htable, _⟩ := lookupSortColumns_correct _ _ _ b t hsort
  have hb : b.length = usable := by simpa only [List.length_ofFn] using hinput.length_eq
  have ht : t.length = usable := by simpa only [List.length_ofFn] using htable.length_eq
  have hbList : List.ofFn (fun i : Fin usable => b.getD i.val 0) = b := by
    rw [← hb]
    exact ofFn_getD_eq b 0
  have htList : List.ofFn (fun i : Fin usable => t.getD i.val 0) = t := by
    rw [← ht]
    exact ofFn_getD_eq t 0
  refine ⟨hb, ht, ?_, ?_, lookupSortColumns_first _ _ _ b t 0 hsort, ?_⟩
  · rw [hbList]
    exact hinput.symm
  · rw [htList]
    exact htable.symm
  · intro i hpos hi
    exact lookupSortColumns_run _ _ _ b t 0 hsort i hpos (by omega)

theorem lookupExpressions_zero_of_sort
    (usable row : ℕ) (input table : ℕ → Fp) (b t : List Fp)
    (hsort : lookupSortedPrefixes usable input table = some (b, t))
    (z next previous : ℕ → Fp) (inputExprs tableExprs : List (Expr Fp))
    (fixed advice instanceRows : ℕ → ℕ → Fp) (theta beta gamma : Fp)
    (hinput : ∀ i < usable, compressExprs (fixed i) (advice i) (instanceRows i) theta inputExprs = input i)
    (htable : ∀ i < usable, compressExprs (fixed i) (advice i) (instanceRows i) theta tableExprs = table i)
    (hz : ∀ i ≤ usable, z i = lookupProductRows input table
      (fun j => b.getD j 0) (fun j => t.getD j 0) beta gamma i)
    (hnext : ∀ i < usable, next i = z (i + 1))
    (hprevious : ∀ i, 0 < i → i < usable → previous i = b.getD (i - 1) 0)
    (hden : ∀ i < usable, b.getD i 0 + beta ≠ 0 ∧ t.getD i 0 + gamma ≠ 0) :
    lookupExpressions (lookupRowEvaluations z next (fun j => b.getD j 0) previous (fun j => t.getD j 0) row)
      inputExprs tableExprs (fixed row) (advice row) (instanceRows row) theta beta gamma
      (rowSelectorValues (F := Fp) usable row).1 (rowSelectorValues (F := Fp) usable row).2.1
      (rowSelectorValues (F := Fp) usable row).2.2 = List.replicate 5 0 := by
  obtain ⟨_, _, hinputPerm, htablePerm, hfirst, hrun⟩ := lookupSortedPrefixes_correct usable input table b t hsort
  exact lookupExpressions_zero_of_scan input table (fun j => b.getD j 0) (fun j => t.getD j 0)
    z next previous inputExprs tableExprs fixed advice instanceRows theta beta gamma usable row
    hinput htable hz hnext hprevious hinputPerm htablePerm hfirst hrun hden

end Zcash.Snark.ZeroKnowledge
