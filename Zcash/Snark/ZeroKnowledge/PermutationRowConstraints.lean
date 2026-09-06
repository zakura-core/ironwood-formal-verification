import Zcash.Snark.ZeroKnowledge.LookupRowConstraints

/-!
# The computed permutation scans satisfy the verifier's row constraints

The factors and constraints use the existing three-chunk verifier layout and its exact
column-name stride. Chunk zero starts at one; later chunks inherit the preceding terminal
state. Only the first-row use of each terminal rotation is constrained, and masked rows
remain arbitrary where the selectors switch the checks off.

Copy-preserving wiring gives a full product identity on named cells. Instantiating this
identity at the actual packed column/chunk routing and proving agreement with the masked
column constructor remain separate obligations.
-/

namespace Zcash.Snark.ZeroKnowledge

open Finset

variable {F : Type*} [Field F]

/-- A copy-preserving permutation equates the full named-factor products for every challenge. -/
theorem copyPermutation_product_identity {I : Type*} [Fintype I]
    (sigma : Equiv.Perm I) (value name : I → F) (beta gamma : F)
    (hcopy : ∀ i, value i = value (sigma i)) :
    (∏ i, (value i + beta * name i + gamma)) =
      ∏ i, (value i + beta * name (sigma i) + gamma) := by
  symm
  exact Fintype.prod_equiv sigma (fun i => value i + beta * name (sigma i) + gamma)
    (fun i => value i + beta * name i + gamma) (fun i => by
      dsimp only
      rw [hcopy i])

/-- The identity-named product in the verifier's chunk recurrence. -/
def permutationRowNumerator (pairs : ℕ → ℕ → List (F × F)) (beta gamma omega delta : F)
    (chunkLen chunk row : ℕ) : F :=
  ∏ j ∈ range (pairs chunk row).length,
    (((pairs chunk row).getD j (0, 0)).1 + beta * omega ^ row * delta ^ (chunk * chunkLen) * delta ^ j + gamma)

/-- The sigma-named product in the verifier's chunk recurrence. -/
def permutationRowDenominator (pairs : ℕ → ℕ → List (F × F)) (beta gamma : F)
    (chunk row : ℕ) : F :=
  ∏ j ∈ range (pairs chunk row).length,
    (((pairs chunk row).getD j (0, 0)).1 + beta * ((pairs chunk row).getD j (0, 0)).2 + gamma)

/-- Product scans with inherited chunk seeds and zero-preserving inversion. -/
def permutationScanRows (pairs : ℕ → ℕ → List (F × F)) (beta gamma omega delta : F)
    (chunkLen usable : ℕ) : ℕ → ℕ → F :=
  chainedProductRows (permutationRowNumerator pairs beta gamma omega delta chunkLen)
    (permutationRowDenominator pairs beta gamma) usable

/-- The three-chunk proof layout carries a terminal rotation for the first two chunks. -/
def permutationRowEvaluations (z next last : ℕ → ℕ → F) (chunk row : ℕ) : PermSetEval F where
  eval := z chunk row
  nextEval := next chunk row
  lastEval := if chunk < 2 then some (last chunk row) else none

/-- One actual chunk constraint follows from the computed scan outside zero denominators. -/
theorem permChunkExpression_zero_of_scan
    (pairs : ℕ → ℕ → List (F × F)) (beta gamma omega delta : F)
    (chunkLen usable chunk row : ℕ) (z next last : ℕ → ℕ → F)
    (hz : ∀ i ≤ usable, z chunk i = permutationScanRows pairs beta gamma omega delta chunkLen usable chunk i)
    (hnext : ∀ i < usable, next chunk i = z chunk (i + 1))
    (hden : ∀ i < usable, permutationRowDenominator pairs beta gamma chunk i ≠ 0) :
    permChunkExpression beta gamma (omega ^ row) delta chunkLen chunk
      (permutationRowEvaluations z next last chunk row) (pairs chunk row)
      (rowSelectorValues (F := F) usable row).2.1 (rowSelectorValues (F := F) usable row).2.2 = 0 := by
  rw [permChunkExpression_eq, rowSelectorValues_active]
  dsimp only [permutationRowEvaluations]
  by_cases hrow : row < usable
  · rw [if_pos hrow, mul_one, hnext row hrow, hz (row + 1) (by omega), hz row (by omega)]
    exact sub_eq_zero.mpr (chainedProductRows_recurrence
      (permutationRowNumerator pairs beta gamma omega delta chunkLen)
      (permutationRowDenominator pairs beta gamma) usable chunk row (hden row hrow))
  · rw [if_neg hrow, mul_zero]

/-- The three computed chunks satisfy all seven existing permutation constraints.

The global product identity supplies the final boundary rule even on zero factors;
the nonzero-denominator premise is used only for the active-row recurrences. -/
theorem permutationExpressions_zero_of_scan
    (pairs : ℕ → ℕ → List (F × F)) (beta gamma omega delta : F)
    (chunkLen usable row : ℕ) (z next last : ℕ → ℕ → F)
    (hz : ∀ c < 3, ∀ i ≤ usable,
      z c i = permutationScanRows pairs beta gamma omega delta chunkLen usable c i)
    (hnext : ∀ c < 3, ∀ i < usable, next c i = z c (i + 1))
    (hlast : ∀ c < 2, last c 0 = z c usable)
    (hproduct : (∏ c ∈ range 3, ∏ i ∈ range usable,
        permutationRowNumerator pairs beta gamma omega delta chunkLen c i) =
      ∏ c ∈ range 3, ∏ i ∈ range usable, permutationRowDenominator pairs beta gamma c i)
    (hden : ∀ c < 3, ∀ i < usable, permutationRowDenominator pairs beta gamma c i ≠ 0) :
    let sets := fun c => permutationRowEvaluations z next last c row
    permutationExpressions [sets 0, sets 1, sets 2]
      [(sets 0, pairs 0 row), (sets 1, pairs 1 row), (sets 2, pairs 2 row)]
      beta gamma (omega ^ row) delta chunkLen
      (rowSelectorValues (F := F) usable row).1 (rowSelectorValues (F := F) usable row).2.1
      (rowSelectorValues (F := F) usable row).2.2 = List.replicate 7 0 := by
  have hstart : (rowSelectorValues (F := F) usable row).1 * (1 - z 0 row) = 0 := by
    have hz0 : z 0 0 = 1 := (hz 0 (by decide) 0 (Nat.zero_le usable)).trans
      (chainedProductRows_start _ _ usable)
    by_cases hrow : row = 0 <;> simp [rowSelectorValues, hrow, hz0]
  have hend : (z 2 row ^ 2 - z 2 row) * (rowSelectorValues (F := F) usable row).2.1 = 0 := by
    have hterminal : z 2 usable ^ 2 - z 2 usable = 0 := by
      rw [hz 2 (by decide) usable le_rfl]
      exact chainedProductRows_terminal_constraint _ _ usable 2 hproduct
    by_cases hrow : row = usable <;> simp [rowSelectorValues, hrow, hterminal]
  have hchain (c : ℕ) (hc : c < 2) :
      (z (c + 1) row - last c row) * (rowSelectorValues (F := F) usable row).1 = 0 := by
    have hboundary : z (c + 1) 0 = last c 0 := by
      rw [hlast c hc, hz (c + 1) (by omega) 0 (Nat.zero_le usable), hz c (by omega) usable le_rfl]
      exact chainedProductRows_chain _ _ usable c
    by_cases hrow : row = 0 <;> simp [rowSelectorValues, hrow, hboundary]
  have hrec (c : ℕ) (hc : c < 3) := permChunkExpression_zero_of_scan pairs beta gamma omega delta
    chunkLen usable c row z next last (hz c hc) (hnext c hc) (hden c hc)
  change [ (rowSelectorValues (F := F) usable row).1 * (1 - z 0 row),
    (z 2 row ^ 2 - z 2 row) * (rowSelectorValues (F := F) usable row).2.1,
    (z 1 row - last 0 row) * (rowSelectorValues (F := F) usable row).1,
    (z 2 row - last 1 row) * (rowSelectorValues (F := F) usable row).1,
    permChunkExpression beta gamma (omega ^ row) delta chunkLen 0
      (permutationRowEvaluations z next last 0 row) (pairs 0 row)
      (rowSelectorValues (F := F) usable row).2.1 (rowSelectorValues (F := F) usable row).2.2,
    permChunkExpression beta gamma (omega ^ row) delta chunkLen 1
      (permutationRowEvaluations z next last 1 row) (pairs 1 row)
      (rowSelectorValues (F := F) usable row).2.1 (rowSelectorValues (F := F) usable row).2.2,
    permChunkExpression beta gamma (omega ^ row) delta chunkLen 2
      (permutationRowEvaluations z next last 2 row) (pairs 2 row)
      (rowSelectorValues (F := F) usable row).2.1 (rowSelectorValues (F := F) usable row).2.2 ] = _
  rw [hstart, hend, hchain 0 (by decide), hchain 1 (by decide),
    hrec 0 (by decide), hrec 1 (by decide), hrec 2 (by decide)]
  rfl

end Zcash.Snark.ZeroKnowledge
