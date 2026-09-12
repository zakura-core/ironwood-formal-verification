import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost
import Zcash.Snark.Verifier.Expressions

/-!
# Counted permutation-chunk constraints

Both running-product folds retain each supplied row-pair access and all field
operations. The delta offset uses an explicit exponent loop at the verifier's
actual declared stride. The result and bound retain inactive rows and all
exceptional field values.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Count both product folds and the inactive-row factor of the actual permutation chunk. -/
def permChunkExpressionCosted {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (beta gamma x delta : F × ℕ) (chunkLen chunkIndex : ℕ)
    (set : PermSetEval (F × ℕ)) (pairs : List ((F × F) × ℕ)) (lLast lBlind : F × ℕ) : F × ℕ :=
  let left := foldlCosted (fun state pair =>
    (state * (pair.1.1 + beta.1 * pair.1.2 + gamma.1),
      pair.2 + beta.2 + gamma.2 + 2 * costs.multiply + 2 * costs.add + 4)) pairs set.nextEval
  let power := fieldPowerCosted costs.multiply delta.1 (chunkIndex * chunkLen)
  let deltaStart := (beta.1 * x.1 * power.1,
    beta.2 + x.2 + delta.2 + power.2 + 2 * costs.multiply + 3)
  let right := foldlCosted (fun state pair =>
    ((state.1 * (pair.1.1 + state.2 + gamma.1), state.2 * delta.1),
      pair.2 + gamma.2 + delta.2 + 2 * costs.multiply + 2 * costs.add + 4))
    pairs ((set.eval.1, deltaStart.1), set.eval.2 + deltaStart.2 + 1)
  fieldMultiplyCosted costs (fieldSubtractCosted costs left (right.1.1, right.2))
    (fieldSubtractCosted costs (1, 1) (fieldAddCosted costs lLast lBlind))

/-- Cost erasure gives the exact verifier expression, including zero and inactive inputs. -/
theorem permChunkExpressionCosted_result {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (beta gamma x delta : F × ℕ) (chunkLen chunkIndex : ℕ)
    (set : PermSetEval (F × ℕ)) (pairs : List ((F × F) × ℕ)) (lLast lBlind : F × ℕ) :
    (permChunkExpressionCosted costs beta gamma x delta chunkLen chunkIndex set pairs lLast lBlind).1 =
      permChunkExpression beta.1 gamma.1 x.1 delta.1 chunkLen chunkIndex
        (set.map Prod.fst) (pairs.map Prod.fst) lLast.1 lBlind.1 := by
  simp only [permChunkExpressionCosted, fieldMultiplyCosted_result, fieldSubtractCosted_result,
    fieldAddCosted_result, foldlCosted_result, fieldPowerCosted_result,
    permChunkExpression, PermSetEval.map, List.foldl_map]

/-- Explicit common-reader budget for both chunk folds and the declared delta exponent. -/
theorem permChunkExpressionCosted_cost_le {F : Type*} [CommRing F] (costs : FieldOperationCosts)
    (beta gamma x delta : F × ℕ) (chunkLen chunkIndex : ℕ)
    (set : PermSetEval (F × ℕ)) (pairs : List ((F × F) × ℕ)) (lLast lBlind : F × ℕ)
    (access : ℕ) (hbeta : beta.2 ≤ access) (hgamma : gamma.2 ≤ access)
    (hx : x.2 ≤ access) (hdelta : delta.2 ≤ access)
    (heval : set.eval.2 ≤ access) (hnext : set.nextEval.2 ≤ access)
    (hpairs : ∀ pair ∈ pairs, pair.2 ≤ access)
    (hlLast : lLast.2 ≤ access) (hlBlind : lBlind.2 ≤ access) :
    (permChunkExpressionCosted costs beta gamma x delta chunkLen chunkIndex set pairs lLast lBlind).2 ≤
      2 * pairs.length * (3 * access + 2 * costs.multiply + 2 * costs.add + 5) +
        (chunkIndex * chunkLen) * (costs.multiply + 1) +
        20 * access + 20 * (costs.add + costs.negate + costs.multiply + 1) := by
  let stepBudget := 3 * access + 2 * costs.multiply + 2 * costs.add + 4
  have hleft := foldlCosted_cost_le_sum (fun state (pair : (F × F) × ℕ) =>
      (state * (pair.1.1 + beta.1 * pair.1.2 + gamma.1),
        pair.2 + beta.2 + gamma.2 + 2 * costs.multiply + 2 * costs.add + 4))
    pairs set.nextEval (fun _ => True) (fun _ => stepBudget) trivial
    (fun _ _ _ _ => trivial) (fun _ _ pair hpair => by
      have h := hpairs pair hpair
      dsimp only [stepBudget]
      omega)
  let power := fieldPowerCosted costs.multiply delta.1 (chunkIndex * chunkLen)
  let deltaStart := (beta.1 * x.1 * power.1,
    beta.2 + x.2 + delta.2 + power.2 + 2 * costs.multiply + 3)
  have hright := foldlCosted_cost_le_sum (fun (state : F × F) (pair : (F × F) × ℕ) =>
      ((state.1 * (pair.1.1 + state.2 + gamma.1), state.2 * delta.1),
        pair.2 + gamma.2 + delta.2 + 2 * costs.multiply + 2 * costs.add + 4))
    pairs ((set.eval.1, deltaStart.1), set.eval.2 + deltaStart.2 + 1)
    (fun _ => True) (fun _ => stepBudget) trivial (fun _ _ _ _ => trivial)
    (fun _ _ pair hpair => by
      have h := hpairs pair hpair
      dsimp only [stepBudget]
      omega)
  have hsum : (pairs.map (fun _ => stepBudget)).sum = pairs.length * stepBudget := by simp
  rw [hsum] at hleft hright
  have hpower : power.2 = (chunkIndex * chunkLen) * (costs.multiply + 1) + 1 :=
    fieldPowerCosted_cost costs.multiply delta.1 (chunkIndex * chunkLen)
  dsimp only [permChunkExpressionCosted, fieldMultiplyCosted, fieldSubtractCosted,
    fieldAddCosted, fieldNegateCosted]
  dsimp only [deltaStart, power] at hright
  dsimp only [power] at hpower
  have hbudget :
      2 * pairs.length * (3 * access + 2 * costs.multiply + 2 * costs.add + 5) =
        2 * (pairs.length * stepBudget) + 2 * pairs.length := by
    dsimp only [stepBudget]
    ring
  rw [hbudget]
  omega

end Zcash.Snark.ZeroKnowledge
