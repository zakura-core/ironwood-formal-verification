import Zcash.Snark.ZeroKnowledge.TranscriptAbsorbCost

/-!
# Counted lookup and permutation transcript blocks

These blocks retain the actual input/table interleaving and the optional last
permutation evaluation. Every present field supplies its full producer cost.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Materialize one original lookup commitment pair, input before table. -/
def absorbLookupPairCosted {F G : Type*} (input table : G × ℕ) : List (TranscriptElt F G) × ℕ :=
  ([.point input.1, .point table.1], input.2 + table.2 + 5)

/-- Materialize every lookup pair in the original proof-major order. -/
def absorbLookupPermutedCosted {F G : Type*} {rows columns : ℕ}
    (input table : Fin rows → Fin columns → G × ℕ) : List (TranscriptElt F G) × ℕ :=
  flattenFinCosted (fun row => flattenFinCosted (fun column =>
    absorbLookupPairCosted (input row column) (table row column)))

/-- Every input/table pair stays adjacent and in its original order. -/
theorem absorbLookupPermutedCosted_result {F G : Type*} {rows columns : ℕ}
    (input table : Fin rows → Fin columns → G × ℕ) :
    (absorbLookupPermutedCosted (F := F) input table).1 =
      absorbLookupPermuted (fun row column => (input row column).1)
        (fun row column => (table row column).1) := by
  simp only [absorbLookupPermutedCosted, flattenFinCosted_result,
    absorbLookupPairCosted, absorbLookupPermuted]

/-- Every lookup contributes exactly its two original commitment items. -/
theorem absorbLookupPermutedCosted_length {F G : Type*} {rows columns : ℕ}
    (input table : Fin rows → Fin columns → G × ℕ) :
    (absorbLookupPermutedCosted (F := F) input table).1.length = rows * (2 * columns) := by
  simp [absorbLookupPermutedCosted, flattenFinCosted_result, absorbLookupPairCosted,
    List.length_flatten, Function.comp_def, Nat.mul_comm]

/-- Both matrix collections and both point producers remain in the pair-block cost. -/
theorem absorbLookupPermutedCosted_cost_le {F G : Type*} {rows columns : ℕ}
    (input table : Fin rows → Fin columns → G × ℕ) (access : ℕ)
    (hinput : ∀ row column, (input row column).2 ≤ access)
    (htable : ∀ row column, (table row column).2 ≤ access) :
    (absorbLookupPermutedCosted (F := F) input table).2 ≤
      rows * (columns * (2 * access + 9) + columns * columns + 2 * columns + 3) + rows * rows + 1 := by
  have hrow (row : Fin rows) :
      (flattenFinCosted (fun column =>
        absorbLookupPairCosted (F := F) (input row column) (table row column))).2 ≤
        columns * (2 * access + 9) + columns * columns + 1 := by
    apply flattenFinCosted_cost_le _ (2 * access + 5) 2
    · intro column
      have hi := hinput row column
      have ht := htable row column
      dsimp only [absorbLookupPairCosted]
      omega
    · intro column
      exact le_rfl
  have hlength (row : Fin rows) :
      (flattenFinCosted (fun column =>
        absorbLookupPairCosted (F := F) (input row column) (table row column))).1.length ≤ 2 * columns := by
    simp [flattenFinCosted_result, absorbLookupPairCosted, List.length_flatten,
      Function.comp_def, Nat.mul_comm]
  have h := flattenFinCosted_cost_le (fun row => flattenFinCosted (fun column =>
      absorbLookupPairCosted (F := F) (input row column) (table row column)))
    (columns * (2 * access + 9) + columns * columns + 1) (2 * columns) hrow hlength
  dsimp only [absorbLookupPermutedCosted]
  convert h using 1
  ring

/-- Materialize the two mandatory permutation claims and the actual optional third claim. -/
def absorbPermSetCosted {F G : Type*} (set : PermSetEval (F × ℕ)) : List (TranscriptElt F G) × ℕ :=
  match set.lastEval with
  | none => ([.scalar set.eval.1, .scalar set.nextEval.1], set.eval.2 + set.nextEval.2 + 5)
  | some last =>
    ([.scalar set.eval.1, .scalar set.nextEval.1, .scalar last.1], set.eval.2 + set.nextEval.2 + last.2 + 7)

/-- The counted block preserves both optional-field branches exactly. -/
theorem absorbPermSetCosted_result {F G : Type*} (set : PermSetEval (F × ℕ)) :
    (absorbPermSetCosted (G := G) set).1 = absorbPermSet (set.map Prod.fst) := by
  cases h : set.lastEval <;> simp [absorbPermSetCosted, absorbPermSet, PermSetEval.map, h]

/-- The original permutation record contributes at most three items. -/
theorem absorbPermSetCosted_length_le {F G : Type*} (set : PermSetEval (F × ℕ)) :
    (absorbPermSetCosted (G := G) set).1.length ≤ 3 := by
  cases h : set.lastEval <;> simp [absorbPermSetCosted, h]

/-- Every present permutation-field producer and optional branch is counted. -/
theorem absorbPermSetCosted_cost_le {F G : Type*} (set : PermSetEval (F × ℕ)) (access : ℕ)
    (hread : permSetReadBound set access) :
    (absorbPermSetCosted (G := G) set).2 ≤ 3 * access + 7 := by
  rcases hread with ⟨hcurrent, hnext, hlast⟩
  cases h : set.lastEval with
  | none => simp only [absorbPermSetCosted, h]; omega
  | some last =>
    have hl := hlast last (by simp [h])
    simp only [absorbPermSetCosted, h]
    omega

/-- Materialize all five original lookup claims in their verifier order. -/
def absorbLookupCosted {F G : Type*} (lookup : LookupEval (F × ℕ)) : List (TranscriptElt F G) × ℕ :=
  ([.scalar lookup.productEval.1, .scalar lookup.productNextEval.1,
    .scalar lookup.permutedInputEval.1, .scalar lookup.permutedInputInvEval.1,
    .scalar lookup.permutedTableEval.1],
   lookup.productEval.2 + lookup.productNextEval.2 + lookup.permutedInputEval.2 +
     lookup.permutedInputInvEval.2 + lookup.permutedTableEval.2 + 11)

/-- Every original lookup claim is retained in exactly the same position. -/
theorem absorbLookupCosted_result {F G : Type*} (lookup : LookupEval (F × ℕ)) :
    (absorbLookupCosted (G := G) lookup).1 = absorbLookup (lookup.map Prod.fst) := rfl

/-- Every original lookup record contributes five scalar items. -/
theorem absorbLookupCosted_length {F G : Type*} (lookup : LookupEval (F × ℕ)) :
    (absorbLookupCosted (G := G) lookup).1.length = 5 := rfl

/-- All five complete scalar-reader costs and their output cells are counted. -/
theorem absorbLookupCosted_cost_le {F G : Type*} (lookup : LookupEval (F × ℕ)) (access : ℕ)
    (hread : lookupEvalReadBound lookup access) :
    (absorbLookupCosted (G := G) lookup).2 ≤ 5 * access + 11 := by
  rcases hread with ⟨h0, h1, h2, h3, h4⟩
  dsimp only [absorbLookupCosted]
  omega

end Zcash.Snark.ZeroKnowledge
