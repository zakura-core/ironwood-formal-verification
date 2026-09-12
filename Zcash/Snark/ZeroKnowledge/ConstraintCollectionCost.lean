import Zcash.Snark.ZeroKnowledge.ConstraintAssemblyCost

/-!
# Counted constraint collection across all sub-proofs

Each sub-proof supplies materialized permutation and lookup inputs together with
their complete preparation costs. Collection retains those costs, evaluates all
constraints, and pays for every concatenated output cell and index adapter.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- The full output size counts every gate, permutation boundary, and lookup constraint. -/
theorem subProofConstraintsCosted_length_le {F : Type*} [CommRing F]
    (costs : FieldOperationCosts) (node : ℕ) (fixed advice instanceRead : ℕ → F × ℕ)
    (gates : List (Expr F)) (sets : List (PermSetEval (F × ℕ)))
    (chunks : List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)))
    (lookups : List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F)))
    (beta gamma x delta theta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ) :
    (subProofConstraintsCosted costs node fixed advice instanceRead gates sets chunks lookups
      beta gamma x delta theta chunkLen l0 lLast lBlind).1.length ≤
      gates.length + sets.length + chunks.length + 5 * lookups.length + 2 := by
  have hpermutation := permutationExpressionsCosted_length_le costs sets chunks
    beta gamma x delta chunkLen l0 lLast lBlind
  have hlookups : (flatMapListCosted (fun lookup =>
      lookupExpressionsCosted costs node lookup.1 lookup.2.1 lookup.2.2 fixed advice instanceRead
        theta beta gamma l0 lLast lBlind) lookups).1.length = 5 * lookups.length := by
    rw [flatMapListCosted_result, List.length_flatMap]
    simp [lookupExpressionsCosted_length, Nat.mul_comm]
  simp only [subProofConstraintsCosted, appendListCosted_result, List.length_append,
    mapListCosted_result, List.length_map, hlookups]
  omega

/-- Evaluate all sub-proofs, retaining every input-provider cost and materializing the ordered result. -/
def allConstraintsCosted {F : Type*} [CommRing F] {count : ℕ}
    (costs : FieldOperationCosts) (node : ℕ) (fixed : ℕ → F × ℕ)
    (advice instanceRead : Fin count → ℕ → F × ℕ) (gates : List (Expr F))
    (sets : Fin count → List (PermSetEval (F × ℕ)) × ℕ)
    (chunks : Fin count → List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)) × ℕ)
    (lookups : Fin count → List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F)) × ℕ)
    (beta gamma x delta theta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ) : List F × ℕ :=
  flattenFinCosted fun index =>
    let setInputs := sets index
    let chunkInputs := chunks index
    let lookupInputs := lookups index
    let result := subProofConstraintsCosted costs node fixed (advice index) (instanceRead index)
      gates setInputs.1 chunkInputs.1 lookupInputs.1 beta gamma x delta theta chunkLen l0 lLast lBlind
    (result.1, setInputs.2 + chunkInputs.2 + lookupInputs.2 + result.2 + 1)

/-- Erasure is exactly the verifier's complete cross-sub-proof constraint list. -/
theorem allConstraintsCosted_result {F : Type*} [CommRing F] {count : ℕ}
    (costs : FieldOperationCosts) (node : ℕ) (fixed : ℕ → F × ℕ)
    (advice instanceRead : Fin count → ℕ → F × ℕ) (gates : List (Expr F))
    (sets : Fin count → List (PermSetEval (F × ℕ)) × ℕ)
    (chunks : Fin count → List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)) × ℕ)
    (lookups : Fin count → List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F)) × ℕ)
    (beta gamma x delta theta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ) :
    (allConstraintsCosted costs node fixed advice instanceRead gates sets chunks lookups
      beta gamma x delta theta chunkLen l0 lLast lBlind).1 =
      allConstraints (fun index => (fixed index).1) (fun action index => (advice action index).1)
        (fun action index => (instanceRead action index).1) gates
        (fun action => (sets action).1.map (PermSetEval.map Prod.fst))
        (fun action => (chunks action).1.map (fun chunk => (chunk.1.map Prod.fst, chunk.2.map Prod.fst)))
        (fun action => (lookups action).1.map (fun lookup => (lookup.1.map Prod.fst, lookup.2.1, lookup.2.2)))
        beta.1 gamma.1 x.1 delta.1 theta.1 chunkLen l0.1 lLast.1 lBlind.1 := by
  simp only [allConstraintsCosted, flattenFinCosted_result, subProofConstraintsCosted_result,
    allConstraints]

/-- A complete collection bound from materialized input sizes and separately retained provider costs. -/
theorem allConstraintsCosted_cost_le {F : Type*} [CommRing F] {count : ℕ}
    (costs : FieldOperationCosts) (node access preparation budget length : ℕ)
    (fixed : ℕ → F × ℕ) (advice instanceRead : Fin count → ℕ → F × ℕ) (gates : List (Expr F))
    (sets : Fin count → List (PermSetEval (F × ℕ)) × ℕ)
    (chunks : Fin count → List (PermSetEval (F × ℕ) × List ((F × F) × ℕ)) × ℕ)
    (lookups : Fin count → List (LookupEval (F × ℕ) × List (Expr F) × List (Expr F)) × ℕ)
    (beta gamma x delta theta : F × ℕ) (chunkLen : ℕ) (l0 lLast lBlind : F × ℕ)
    (hfixed : ∀ index, (fixed index).2 ≤ access)
    (hadvice : ∀ action index, (advice action index).2 ≤ access)
    (hinstance : ∀ action index, (instanceRead action index).2 ≤ access)
    (hsets : ∀ action set, set ∈ (sets action).1 → permSetReadBound set access)
    (hchunks : ∀ action chunk, chunk ∈ (chunks action).1 →
      permSetReadBound chunk.1 access ∧ ∀ pair ∈ chunk.2, pair.2 ≤ access)
    (hlookups : ∀ action lookup, lookup ∈ (lookups action).1 → lookupEvalReadBound lookup.1 access)
    (hprepare : ∀ action, (sets action).2 + (chunks action).2 + (lookups action).2 ≤ preparation)
    (hbudget : ∀ action, subProofConstraintCostBudget costs node access gates
      (sets action).1 (chunks action).1 (lookups action).1 chunkLen ≤ budget)
    (hlength : ∀ action, gates.length + (sets action).1.length + (chunks action).1.length +
      5 * (lookups action).1.length + 2 ≤ length)
    (hbeta : beta.2 ≤ access) (hgamma : gamma.2 ≤ access) (hx : x.2 ≤ access)
    (hdelta : delta.2 ≤ access) (htheta : theta.2 ≤ access)
    (hl0 : l0.2 ≤ access) (hlLast : lLast.2 ≤ access) (hlBlind : lBlind.2 ≤ access) :
    (allConstraintsCosted costs node fixed advice instanceRead gates sets chunks lookups
      beta gamma x delta theta chunkLen l0 lLast lBlind).2 ≤
      count * (preparation + budget + length + 3) + count * count + 1 := by
  rw [show preparation + budget + length + 3 = preparation + budget + 1 + length + 2 by omega]
  unfold allConstraintsCosted
  apply flattenFinCosted_cost_le (budget := preparation + budget + 1) (length := length)
  · intro action
    have h := subProofConstraintsCosted_cost_le costs node access fixed (advice action) (instanceRead action)
      gates (sets action).1 (chunks action).1 (lookups action).1 beta gamma x delta theta chunkLen
      l0 lLast lBlind hfixed (hadvice action) (hinstance action) (hsets action) (hchunks action)
      (hlookups action) hbeta hgamma hx hdelta htheta hl0 hlLast hlBlind
    have hp := hprepare action
    have hb := hbudget action
    dsimp only
    omega
  · intro action
    exact (subProofConstraintsCosted_length_le costs node fixed (advice action) (instanceRead action)
      gates (sets action).1 (chunks action).1 (lookups action).1 beta gamma x delta theta chunkLen
      l0 lLast lBlind).trans (hlength action)

end Zcash.Snark.ZeroKnowledge
