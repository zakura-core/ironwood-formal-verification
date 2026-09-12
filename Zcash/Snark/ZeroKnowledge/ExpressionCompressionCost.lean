import Zcash.Snark.ZeroKnowledge.ExpressionCost
import Zcash.Snark.ZeroKnowledge.ListFoldCost

/-!+# Counted lookup-expression compression

The evaluator traverses every original expression and carries the complete query
cost into the ordered compression fold. The bound is linear in the total number
of AST nodes and in the list length, with all arithmetic prices explicit.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Count the actual lookup compression fold, including expression evaluation at every step. -/
def compressExprsCosted {F : Type*} [CommRing F] (node add negate multiply : ℕ)
    (fixed advice instanceRead : ℕ → F × ℕ) (theta : F × ℕ) (expressions : List (Expr F)) : F × ℕ :=
  foldlCosted (fun state expression =>
    let value := exprEvalCosted node add negate multiply fixed advice instanceRead expression
    (state * theta.1 + value.1, value.2 + theta.2 + multiply + add + 1)) expressions (0, 1)

/-- Erasing the counter gives the verifier's original expression compression. -/
theorem compressExprsCosted_result {F : Type*} [CommRing F] (node add negate multiply : ℕ)
    (fixed advice instanceRead : ℕ → F × ℕ) (theta : F × ℕ) (expressions : List (Expr F)) :
    (compressExprsCosted node add negate multiply fixed advice instanceRead theta expressions).1 =
      compressExprs (fun index => (fixed index).1) (fun index => (advice index).1)
        (fun index => (instanceRead index).1) theta.1 expressions := by
  simp only [compressExprsCosted, foldlCosted_result, exprEvalCosted_result, compressExprs]

/-- The complete compression bound includes AST traversal, query readers, and all Horner steps. -/
theorem compressExprsCosted_cost_le {F : Type*} [CommRing F] (node add negate multiply : ℕ)
    (fixed advice instanceRead : ℕ → F × ℕ) (theta : F × ℕ) (expressions : List (Expr F))
    (access : ℕ) (hfixed : ∀ index, (fixed index).2 ≤ access)
    (hadvice : ∀ index, (advice index).2 ≤ access)
    (hinstance : ∀ index, (instanceRead index).2 ≤ access) :
    (compressExprsCosted node add negate multiply fixed advice instanceRead theta expressions).2 ≤
      (expressions.map exprNodeCount).sum * (node + 1 + access + add + negate + multiply) +
        expressions.length * (theta.2 + multiply + add + 2) + 2 := by
  let unit := node + 1 + access + add + negate + multiply
  let overhead := theta.2 + multiply + add + 1
  have h := foldlCosted_cost_le_sum (fun state expression =>
      let value := exprEvalCosted node add negate multiply fixed advice instanceRead expression
      (state * theta.1 + value.1, value.2 + theta.2 + multiply + add + 1))
    expressions (0, 1) (fun _ => True) (fun expression => exprNodeCount expression * unit + overhead)
    trivial (fun _ _ _ _ => trivial) (fun _ _ expression _ => by
      have he := exprEvalCosted_cost_le node add negate multiply fixed advice instanceRead
        expression access hfixed hadvice hinstance
      dsimp only [unit, overhead]
      omega)
  have hsum :
      (expressions.map (fun expression => exprNodeCount expression * unit + overhead)).sum =
        (expressions.map exprNodeCount).sum * unit + expressions.length * overhead := by
    clear h
    induction expressions with
    | nil => simp
    | cons expression rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring
  rw [hsum] at h
  dsimp only [compressExprsCosted]
  calc
    _ ≤ 1 + ((expressions.map exprNodeCount).sum * unit + expressions.length * overhead) +
        expressions.length + 1 := h
    _ = _ := by dsimp only [unit, overhead]; ring

end Zcash.Snark.ZeroKnowledge
