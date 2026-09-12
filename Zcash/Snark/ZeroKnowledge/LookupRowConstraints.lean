import Zcash.Snark.ZeroKnowledge.RunningProductRows
import Zcash.Snark.Verifier.Expressions

/-!
# The computed lookup scan satisfies the verifier's five row constraints

The actual `lookupExpressions` builder is used. The product column agrees with the
computed ratio scan through the retained terminal row, while next/previous rotations
agree only where the recurrence uses them. Values on masked rows remain arbitrary.
The proof derives every constraint from the scan, the input/table permutation laws,
and the sorted columns' run structure, outside zero denominator factors.

`LookupSortRows` supplies the sorting premises from the specified algorithm. The column
schedule must still establish compression and scan agreement. These are row-construction
facts; the theorem does not assume the lookup constraint polynomials vanish.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F : Type*} [Field F]

/-- The first-row, terminal-row, and blinding-row selector values. -/
def rowSelectorValues (usable row : ℕ) : F × F × F :=
  (if row = 0 then 1 else 0, if row = usable then 1 else 0, if usable < row then 1 else 0)

/-- The product and run recurrences apply exactly before the retained terminal row. -/
theorem rowSelectorValues_active (usable row : ℕ) :
    1 - ((rowSelectorValues (F := F) usable row).2.1 +
      (rowSelectorValues (F := F) usable row).2.2) = if row < usable then 1 else 0 := by
  by_cases h : row < usable
  · have he : row ≠ usable := by omega
    have hn : ¬ usable < row := by omega
    simp [rowSelectorValues, h, he, hn]
  · by_cases he : row = usable
    · subst row
      simp [rowSelectorValues]
    · have hn : usable < row := by omega
      simp [rowSelectorValues, h, he, hn]

/-- The verifier's lookup evaluation record at a row, retaining both rotated values. -/
def lookupRowEvaluations (z next b previous t : ℕ → F) (row : ℕ) : LookupEval F where
  productEval := z row
  productNextEval := next row
  permutedInputEval := b row
  permutedInputInvEval := previous row
  permutedTableEval := t row

/-- All five existing lookup constraints vanish for the computed scan on nonexceptional inputs.

The product terminal check does not require nonzero factors; the recurrence does.
Rotated or masked values that are switched off by selectors are unrestricted. -/
theorem lookupExpressions_zero_of_scan
    (input table b t z next previous : ℕ → F)
    (inputExprs tableExprs : List (Expr F))
    (fixed advice instanceRows : ℕ → ℕ → F) (theta beta gamma : F) (usable row : ℕ)
    (hinput : ∀ i < usable, compressExprs (fixed i) (advice i) (instanceRows i) theta inputExprs = input i)
    (htable : ∀ i < usable, compressExprs (fixed i) (advice i) (instanceRows i) theta tableExprs = table i)
    (hz : ∀ i ≤ usable, z i = lookupProductRows input table b t beta gamma i)
    (hnext : ∀ i < usable, next i = z (i + 1))
    (hprevious : ∀ i, 0 < i → i < usable → previous i = b (i - 1))
    (hinputPerm : (List.ofFn fun i : Fin usable => input i.val).Perm
      (List.ofFn fun i : Fin usable => b i.val))
    (htablePerm : (List.ofFn fun i : Fin usable => table i.val).Perm
      (List.ofFn fun i : Fin usable => t i.val))
    (hfirst : b 0 = t 0)
    (hrun : ∀ i, 0 < i → i < usable → b i = t i ∨ b i = b (i - 1))
    (hden : ∀ i < usable, b i + beta ≠ 0 ∧ t i + gamma ≠ 0) :
    lookupExpressions (lookupRowEvaluations z next b previous t row) inputExprs tableExprs
      (fixed row) (advice row) (instanceRows row) theta beta gamma
      (rowSelectorValues (F := F) usable row).1
      (rowSelectorValues (F := F) usable row).2.1
      (rowSelectorValues (F := F) usable row).2.2 = List.replicate 5 0 := by
  have hz0 : z 0 = 1 := by
    simpa only [lookupProductRows, runningProductRows_zero] using hz 0 (Nat.zero_le usable)
  have hzEnd : z usable ^ 2 - z usable = 0 := by
    rw [hz usable le_rfl]
    exact lookupProductRows_terminal_constraint input table b t beta gamma usable hinputPerm htablePerm
  have hstart : (rowSelectorValues (F := F) usable row).1 * (1 - z row) = 0 := by
    by_cases hrow : row = 0 <;> simp [rowSelectorValues, hrow, hz0]
  have hend : (rowSelectorValues (F := F) usable row).2.1 * (z row ^ 2 - z row) = 0 := by
    by_cases hrow : row = usable <;> simp [rowSelectorValues, hrow, hzEnd]
  have hrec : (next row * (b row + beta) * (t row + gamma) - z row *
        (compressExprs (fixed row) (advice row) (instanceRows row) theta inputExprs + beta) *
        (compressExprs (fixed row) (advice row) (instanceRows row) theta tableExprs + gamma)) *
      (1 - ((rowSelectorValues (F := F) usable row).2.1 +
        (rowSelectorValues (F := F) usable row).2.2)) = 0 := by
    rw [rowSelectorValues_active]
    by_cases hrow : row < usable
    · rw [if_pos hrow, mul_one, hinput row hrow, htable row hrow, hnext row hrow,
        hz (row + 1) (by omega), hz row (Nat.le_of_lt hrow)]
      exact sub_eq_zero.mpr (lookupProductRows_recurrence input table b t beta gamma row
        (hden row hrow).1 (hden row hrow).2)
    · rw [if_neg hrow, mul_zero]
  have hfirstTerm : (rowSelectorValues (F := F) usable row).1 * (b row - t row) = 0 := by
    by_cases hrow : row = 0 <;> simp [rowSelectorValues, hrow, hfirst]
  have hrunTerm : (b row - t row) * (b row - previous row) *
      (1 - ((rowSelectorValues (F := F) usable row).2.1 +
        (rowSelectorValues (F := F) usable row).2.2)) = 0 := by
    rw [rowSelectorValues_active]
    by_cases hrow : row < usable
    · rw [if_pos hrow, mul_one]
      by_cases hzero : row = 0
      · simp [hzero, hfirst]
      · have hpos : 0 < row := by omega
        rcases hrun row hpos hrow with h | h
        · simp [h]
        · rw [hprevious row hpos hrow, h, sub_self, mul_zero]
    · rw [if_neg hrow, mul_zero]
  rw [lookupExpressions_eq]
  dsimp only [lookupRowEvaluations]
  rw [hstart, hend, hrec, hfirstTerm, hrunTerm]
  rfl

end Zcash.Snark.ZeroKnowledge
