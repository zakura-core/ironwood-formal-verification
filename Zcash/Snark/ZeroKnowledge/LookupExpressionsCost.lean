import Zcash.Snark.ZeroKnowledge.ExpressionCompressionCost
import Zcash.Snark.ZeroKnowledge.FieldArithmeticCost

/-!
# Counted evaluation of the verifier's lookup constraints

Both input and table expression trees are evaluated by the counted compression
algorithm. All five constraint values are materialized. The bound charges every
input access and field operation, and preserves the original inactive-row and
exceptional-value behavior without any challenge exclusion.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Compression budget with a uniform complete query and challenge access bound. -/
def lookupCompressionCostBudget {F : Type*} (costs : FieldOperationCosts) (node access : ℕ)
    (expressions : List (Expr F)) : ℕ :=
  (expressions.map exprNodeCount).sum * (node + 1 + access + costs.add + costs.negate + costs.multiply) +
    expressions.length * (access + costs.multiply + costs.add + 2) + 2

/-- Count and materialize all five lookup constraints using the actual verifier formulas. -/
def lookupExpressionsCosted {F : Type*} [CommRing F] (costs : FieldOperationCosts) (node : ℕ)
    (le : LookupEval (F × ℕ)) (inputExprs tableExprs : List (Expr F))
    (fixed advice instanceRead : ℕ → F × ℕ) (theta beta gamma l0 lLast lBlind : F × ℕ) : List F × ℕ :=
  let one : F × ℕ := (1, 1)
  let active := fieldSubtractCosted costs one (fieldAddCosted costs lLast lBlind)
  let left := fieldMultiplyCosted costs
    (fieldMultiplyCosted costs le.productNextEval (fieldAddCosted costs le.permutedInputEval beta))
    (fieldAddCosted costs le.permutedTableEval gamma)
  let input := compressExprsCosted node costs.add costs.negate costs.multiply fixed advice instanceRead theta inputExprs
  let table := compressExprsCosted node costs.add costs.negate costs.multiply fixed advice instanceRead theta tableExprs
  let right := fieldMultiplyCosted costs
    (fieldMultiplyCosted costs le.productEval (fieldAddCosted costs input beta))
    (fieldAddCosted costs table gamma)
  mapListCosted (fun value => value)
    [fieldMultiplyCosted costs l0 (fieldSubtractCosted costs one le.productEval),
      fieldMultiplyCosted costs lLast
        (fieldSubtractCosted costs (fieldMultiplyCosted costs le.productEval le.productEval) le.productEval),
      fieldMultiplyCosted costs (fieldSubtractCosted costs left right) active,
      fieldMultiplyCosted costs l0 (fieldSubtractCosted costs le.permutedInputEval le.permutedTableEval),
      fieldMultiplyCosted costs
        (fieldMultiplyCosted costs (fieldSubtractCosted costs le.permutedInputEval le.permutedTableEval)
          (fieldSubtractCosted costs le.permutedInputEval le.permutedInputInvEval)) active]

/-- Every materialized constraint equals the existing verifier's corresponding lookup expression. -/
theorem lookupExpressionsCosted_result {F : Type*} [CommRing F] (costs : FieldOperationCosts) (node : ℕ)
    (le : LookupEval (F × ℕ)) (inputExprs tableExprs : List (Expr F))
    (fixed advice instanceRead : ℕ → F × ℕ) (theta beta gamma l0 lLast lBlind : F × ℕ) :
    (lookupExpressionsCosted costs node le inputExprs tableExprs fixed advice instanceRead
      theta beta gamma l0 lLast lBlind).1 =
      lookupExpressions (le.map Prod.fst) inputExprs tableExprs
        (fun index => (fixed index).1) (fun index => (advice index).1)
        (fun index => (instanceRead index).1) theta.1 beta.1 gamma.1 l0.1 lLast.1 lBlind.1 := by
  simp only [lookupExpressionsCosted, mapListCosted_result, List.map_cons, List.map_nil,
    fieldMultiplyCosted_result, fieldSubtractCosted_result, fieldAddCosted_result,
    compressExprsCosted_result, lookupExpressions, LookupEval.map, pow_two]

/-- All five supplied lookup readings retain a common complete access bound. -/
def lookupEvalReadBound {F : Type*} (le : LookupEval (F × ℕ)) (access : ℕ) : Prop :=
  le.productEval.2 ≤ access ∧ le.productNextEval.2 ≤ access ∧
    le.permutedInputEval.2 ≤ access ∧ le.permutedInputInvEval.2 ≤ access ∧ le.permutedTableEval.2 ≤ access

/-- Both AST compressions and all five output expressions fit an explicit complete arithmetic budget. -/
theorem lookupExpressionsCosted_cost_le {F : Type*} [CommRing F] (costs : FieldOperationCosts) (node : ℕ)
    (le : LookupEval (F × ℕ)) (inputExprs tableExprs : List (Expr F))
    (fixed advice instanceRead : ℕ → F × ℕ) (theta beta gamma l0 lLast lBlind : F × ℕ)
    (access : ℕ) (hle : lookupEvalReadBound le access)
    (hfixed : ∀ index, (fixed index).2 ≤ access) (hadvice : ∀ index, (advice index).2 ≤ access)
    (hinstance : ∀ index, (instanceRead index).2 ≤ access)
    (htheta : theta.2 ≤ access) (hbeta : beta.2 ≤ access) (hgamma : gamma.2 ≤ access)
    (hl0 : l0.2 ≤ access) (hlLast : lLast.2 ≤ access) (hlBlind : lBlind.2 ≤ access) :
    (lookupExpressionsCosted costs node le inputExprs tableExprs fixed advice instanceRead
      theta beta gamma l0 lLast lBlind).2 ≤
      lookupCompressionCostBudget costs node access inputExprs +
        lookupCompressionCostBudget costs node access tableExprs +
        50 * access + 100 * (costs.add + costs.negate + costs.multiply + 1) := by
  have hcompression (expressions : List (Expr F)) :
      (compressExprsCosted node costs.add costs.negate costs.multiply fixed advice instanceRead theta expressions).2 ≤
        lookupCompressionCostBudget costs node access expressions := by
    refine (compressExprsCosted_cost_le node costs.add costs.negate costs.multiply fixed advice instanceRead theta
      expressions access hfixed hadvice hinstance).trans ?_
    unfold lookupCompressionCostBudget
    gcongr
  have hinput := hcompression inputExprs
  have htable := hcompression tableExprs
  rcases hle with ⟨hp, hpn, ha, hai, hs⟩
  dsimp only [lookupExpressionsCosted, mapListCosted, fieldAddCosted, fieldSubtractCosted,
    fieldNegateCosted, fieldMultiplyCosted]
  omega

end Zcash.Snark.ZeroKnowledge
