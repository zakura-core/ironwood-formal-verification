import Zcash.Snark.ZeroKnowledge.RunningProductRows
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost

/-!
# Counted real-prover product scans

Every ratio step retains the costs of its numerator, denominator, and inherited
state. Total field inversion preserves the reference behavior at zero. The
bounds apply to every input value and do not require valid rows or nonzero
denominators.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F : Type*} [Field F]

/-- Execute the original exclusive ratio recurrence with complete operand costs. -/
def runningProductRowsCosted (costs : FieldOperationCosts) (num den : ℕ → F × ℕ)
    (initial : F × ℕ) : ℕ → F × ℕ
  | 0 => (initial.1, initial.2 + 1)
  | row + 1 =>
    let previous := runningProductRowsCosted costs num den initial row
    let value := fieldDivideCosted costs (fieldMultiplyCosted costs previous (num row)) (den row)
    (value.1, value.2 + 2)

/-- Every value agrees with the reference ratio recurrence, including division by zero. -/
theorem runningProductRowsCosted_result (costs : FieldOperationCosts) (num den : ℕ → F × ℕ)
    (initial : F × ℕ) (rows : ℕ) :
    (runningProductRowsCosted costs num den initial rows).1 =
      runningProductRows (fun row => (num row).1) (fun row => (den row).1) initial.1 rows := by
  induction rows <;>
    simp_all only [runningProductRowsCosted, fieldDivideCosted_result,
      fieldMultiplyCosted_result, runningProductRows]

/-- The scan retains complete reader prices and charges every arithmetic operation. -/
theorem runningProductRowsCosted_cost_le (costs : FieldOperationCosts) (num den : ℕ → F × ℕ)
    (initial : F × ℕ) (rows numRead denRead : ℕ)
    (hnum : ∀ row < rows, (num row).2 ≤ numRead)
    (hden : ∀ row < rows, (den row).2 ≤ denRead) :
    (runningProductRowsCosted costs num den initial rows).2 ≤
      initial.2 + rows * (numRead + denRead + 2 * costs.multiply + costs.inverse + 5) + 1 := by
  induction rows with
  | zero => simp [runningProductRowsCosted]
  | succ rows ih =>
    have hp := ih (fun row hrow => hnum row (by omega)) (fun row hrow => hden row (by omega))
    have hn := hnum rows (by omega)
    have hd := hden rows (by omega)
    simp only [runningProductRowsCosted, fieldDivideCosted, fieldMultiplyCosted,
      fieldInverseCosted, Nat.add_mul, Nat.one_mul]
    omega

/-- Compute the actual inherited starting value for each permutation chunk. -/
def chainedProductInitialCosted (costs : FieldOperationCosts) (num den : ℕ → ℕ → F × ℕ)
    (rows : ℕ) : ℕ → F × ℕ
  | 0 => (1, 1)
  | chunk + 1 =>
    let previous := chainedProductInitialCosted costs num den rows chunk
    let value := runningProductRowsCosted costs (num chunk) (den chunk) previous rows
    (value.1, value.2 + 1)

/-- Chained starting values agree with the original chunk order and terminal-state routing. -/
theorem chainedProductInitialCosted_result (costs : FieldOperationCosts) (num den : ℕ → ℕ → F × ℕ)
    (rows chunks : ℕ) :
    (chainedProductInitialCosted costs num den rows chunks).1 =
      chainedProductInitial (fun chunk row => (num chunk row).1)
        (fun chunk row => (den chunk row).1) rows chunks := by
  induction chunks <;>
    simp_all only [chainedProductInitialCosted, runningProductRowsCosted_result, chainedProductInitial]

/-- Every preceding chunk's complete scan is charged in the inherited state. -/
theorem chainedProductInitialCosted_cost_le (costs : FieldOperationCosts)
    (num den : ℕ → ℕ → F × ℕ) (rows chunks numRead denRead : ℕ)
    (hnum : ∀ chunk < chunks, ∀ row < rows, (num chunk row).2 ≤ numRead)
    (hden : ∀ chunk < chunks, ∀ row < rows, (den chunk row).2 ≤ denRead) :
    (chainedProductInitialCosted costs num den rows chunks).2 ≤
      chunks * (rows * (numRead + denRead + 2 * costs.multiply + costs.inverse + 5) + 2) + 1 := by
  induction chunks with
  | zero => simp [chainedProductInitialCosted]
  | succ chunks ih =>
    have hp := ih (fun chunk hchunk => hnum chunk (by omega)) (fun chunk hchunk => hden chunk (by omega))
    have hrun := runningProductRowsCosted_cost_le costs (num chunks) (den chunks)
      (chainedProductInitialCosted costs num den rows chunks) rows numRead denRead
      (hnum chunks (by omega)) (hden chunks (by omega))
    simp only [chainedProductInitialCosted, Nat.add_mul, Nat.one_mul]
    omega

/-- Compute one row using its actual inherited chunk seed. -/
def chainedProductRowsCosted (costs : FieldOperationCosts) (num den : ℕ → ℕ → F × ℕ)
    (rows chunk row : ℕ) : F × ℕ :=
  runningProductRowsCosted costs (num chunk) (den chunk)
    (chainedProductInitialCosted costs num den rows chunk) row

/-- The complete chunk/row computation erases to the original source recurrence. -/
theorem chainedProductRowsCosted_result (costs : FieldOperationCosts) (num den : ℕ → ℕ → F × ℕ)
    (rows chunk row : ℕ) :
    (chainedProductRowsCosted costs num den rows chunk row).1 =
      chainedProductRows (fun chunk row => (num chunk row).1)
        (fun chunk row => (den chunk row).1) rows chunk row := by
  simp only [chainedProductRowsCosted, runningProductRowsCosted_result,
    chainedProductInitialCosted_result, chainedProductRows]

/-- The row budget includes every earlier chunk and the requested prefix of the current one. -/
theorem chainedProductRowsCosted_cost_le (costs : FieldOperationCosts) (num den : ℕ → ℕ → F × ℕ)
    (rows chunk row numRead denRead : ℕ) (hrow : row ≤ rows)
    (hnum : ∀ earlier ≤ chunk, ∀ index < rows, (num earlier index).2 ≤ numRead)
    (hden : ∀ earlier ≤ chunk, ∀ index < rows, (den earlier index).2 ≤ denRead) :
    (chainedProductRowsCosted costs num den rows chunk row).2 ≤
      (chunk * rows + row) * (numRead + denRead + 2 * costs.multiply + costs.inverse + 5) +
        2 * chunk + 2 := by
  have hinit := chainedProductInitialCosted_cost_le costs num den rows chunk numRead denRead
    (fun earlier hearlier => hnum earlier (by omega)) (fun earlier hearlier => hden earlier (by omega))
  have hrun := runningProductRowsCosted_cost_le costs (num chunk) (den chunk)
    (chainedProductInitialCosted costs num den rows chunk) row numRead denRead
    (fun index hindex => hnum chunk le_rfl index (by omega))
    (fun index hindex => hden chunk le_rfl index (by omega))
  change (runningProductRowsCosted costs (num chunk) (den chunk)
    (chainedProductInitialCosted costs num den rows chunk) row).2 ≤ _
  nlinarith

/-- Execute the lookup's original four-factor ratio scan. -/
def lookupProductRowsCosted (costs : FieldOperationCosts)
    (input table permutedInput permutedTable : ℕ → F × ℕ) (beta gamma : F × ℕ) (rows : ℕ) : F × ℕ :=
  runningProductRowsCosted costs
    (fun row => fieldMultiplyCosted costs (fieldAddCosted costs (input row) beta)
      (fieldAddCosted costs (table row) gamma))
    (fun row => fieldMultiplyCosted costs (fieldAddCosted costs (permutedInput row) beta)
      (fieldAddCosted costs (permutedTable row) gamma)) (1, 1) rows

/-- Lookup products preserve their complete source computation for every challenge value. -/
theorem lookupProductRowsCosted_result (costs : FieldOperationCosts)
    (input table permutedInput permutedTable : ℕ → F × ℕ) (beta gamma : F × ℕ) (rows : ℕ) :
    (lookupProductRowsCosted costs input table permutedInput permutedTable beta gamma rows).1 =
      lookupProductRows (fun row => (input row).1) (fun row => (table row).1)
        (fun row => (permutedInput row).1) (fun row => (permutedTable row).1) beta.1 gamma.1 rows := by
  simp only [lookupProductRowsCosted, runningProductRowsCosted_result, fieldMultiplyCosted_result,
    fieldAddCosted_result, lookupProductRows]

/-- All four row providers and both challenge reads are retained in the lookup-scan budget. -/
theorem lookupProductRowsCosted_cost_le (costs : FieldOperationCosts)
    (input table permutedInput permutedTable : ℕ → F × ℕ) (beta gamma : F × ℕ)
    (rows inputRead tableRead permutedInputRead permutedTableRead : ℕ)
    (hinput : ∀ row < rows, (input row).2 ≤ inputRead)
    (htable : ∀ row < rows, (table row).2 ≤ tableRead)
    (hpermutedInput : ∀ row < rows, (permutedInput row).2 ≤ permutedInputRead)
    (hpermutedTable : ∀ row < rows, (permutedTable row).2 ≤ permutedTableRead) :
    (lookupProductRowsCosted costs input table permutedInput permutedTable beta gamma rows).2 ≤
      rows * (inputRead + tableRead + permutedInputRead + permutedTableRead +
        2 * beta.2 + 2 * gamma.2 + 4 * costs.add + 4 * costs.multiply + costs.inverse + 11) + 2 := by
  let num := fun row => fieldMultiplyCosted costs (fieldAddCosted costs (input row) beta)
    (fieldAddCosted costs (table row) gamma)
  let den := fun row => fieldMultiplyCosted costs (fieldAddCosted costs (permutedInput row) beta)
    (fieldAddCosted costs (permutedTable row) gamma)
  have hn (row : ℕ) (hrow : row < rows) :
      (num row).2 ≤ inputRead + tableRead + beta.2 + gamma.2 + 2 * costs.add + costs.multiply + 3 := by
    have hi := hinput row hrow
    have ht := htable row hrow
    dsimp only [num, fieldMultiplyCosted, fieldAddCosted]
    omega
  have hd (row : ℕ) (hrow : row < rows) :
      (den row).2 ≤ permutedInputRead + permutedTableRead + beta.2 + gamma.2 +
        2 * costs.add + costs.multiply + 3 := by
    have hi := hpermutedInput row hrow
    have ht := hpermutedTable row hrow
    dsimp only [den, fieldMultiplyCosted, fieldAddCosted]
    omega
  have h := runningProductRowsCosted_cost_le costs num den (1, 1) rows _ _ hn hd
  change (runningProductRowsCosted costs num den (1, 1) rows).2 ≤ _
  nlinarith

end Zcash.Snark.ZeroKnowledge
