import Zcash.Snark.ZeroKnowledge.PlonkClaimConstraintsCost

/-!
# Materialized length of the complete claim constraint list

The quotient fold consumes the actual concatenated output. Its size follows
from the original gate list and the constructed three-set, three-lookup inputs,
including the verifier's truncating permutation zip.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- A fully collected finite family has at most the sum of its member-length bounds. -/
theorem flattenFinCosted_length_le {α : Type*} {count : ℕ} (values : Fin count → List α × ℕ)
    (length : ℕ) (hlength : ∀ index, (values index).1.length ≤ length) :
    (flattenFinCosted values).1.length ≤ count * length := by
  simp only [flattenFinCosted_result, List.length_flatten, List.map_ofFn, Function.comp_def,
    List.sum_ofFn]
  calc
    ∑ index, (values index).1.length ≤ ∑ _ : Fin count, length :=
      Finset.sum_le_sum (fun index _ => hlength index)
    _ = count * length := by simp

/-- The complete constructed constraint list has at most one gate list plus 23 fields per Action. -/
theorem plonkClaimConstraintsCosted_length_le (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (gates : List (Expr Fp) × ℕ)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    (beta gamma x delta theta : Fp × ℕ) (stride : ℕ) (l0 lLast lBlind : Fp × ℕ) :
    (plonkClaimConstraintsCosted costs node equal read omegaAccess instances fixed sigma views
      gates layout inputs tables beta gamma x delta theta stride l0 lLast lBlind).1.length ≤
      actions * (gates.1.length + 23) := by
  let fixedQueries := plonkFixedQueryCosted costs omegaAccess fixed x
  let adviceQueries := plonkAdviceQueryCosted (actions := actions) equal read views
  let instanceQueries := fun action =>
    publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) x
  let sigmaQueries := publicRowQueryCosted costs omegaAccess sigma x
  let sets := plonkPermutationSetsCosted (actions := actions) equal read views
  let chunks := fun action => permutationQueryChunksCosted (instanceQueries action)
    (adviceQueries action) fixedQueries sigmaQueries (sets action) layout
  let lookups := fun action : Fin actions => plonkLookupInputsCosted equal read views action inputs tables
  unfold plonkClaimConstraintsCosted allConstraintsCosted
  apply flattenFinCosted_length_le
  intro action
  have h := subProofConstraintsCosted_length_le costs node fixedQueries (adviceQueries action)
    (instanceQueries action) gates.1 (sets action).1 (chunks action).1 (lookups action).1
    beta gamma x delta theta stride l0 lLast lBlind
  have hc := permutationQueryChunksCosted_length_le (instanceQueries action) (adviceQueries action)
    fixedQueries sigmaQueries (sets action) layout
  have hp := plonkPermutationSetsCosted_length equal read views action
  have hl := plonkLookupInputsCosted_length equal read views action inputs tables
  change (chunks action).1.length ≤ (sets action).1.length at hc
  change (sets action).1.length = 3 at hp
  change (lookups action).1.length = 3 at hl
  exact h.trans (by omega)

end Zcash.Snark.ZeroKnowledge
