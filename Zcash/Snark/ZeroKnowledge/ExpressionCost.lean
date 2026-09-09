import Zcash.Snark.Verifier.Expressions

/-!
# Counted evaluation of verifier expressions

Evaluation traverses the materialized expression tree and retains the complete
cost of each supplied query reader. Node and field-operation prices are explicit;
constructing the AST and the reader inputs belongs to the surrounding algorithm.
The result theorem identifies the original verifier's evaluator on every index.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Number of actually visited constructor nodes in a materialized verifier expression. -/
def exprNodeCount {F : Type*} : Expr F → ℕ
  | .constant _ | .fixed _ | .advice _ | .instance _ => 1
  | .negated child | .scaled child _ => exprNodeCount child + 1
  | .sum left right | .product left right => exprNodeCount left + exprNodeCount right + 1

/-- Evaluate the actual AST while charging every node, field operation, and supplied query read. -/
def exprEvalCosted {F : Type*} [CommRing F] (node add negate multiply : ℕ)
    (fixed advice instanceRead : ℕ → F × ℕ) : Expr F → F × ℕ
  | .constant value => (value, node + 1)
  | .fixed index => let value := fixed index; (value.1, value.2 + node + 1)
  | .advice index => let value := advice index; (value.1, value.2 + node + 1)
  | .instance index => let value := instanceRead index; (value.1, value.2 + node + 1)
  | .negated child =>
    let value := exprEvalCosted node add negate multiply fixed advice instanceRead child
    (-value.1, value.2 + negate + node + 1)
  | .sum left right =>
    let a := exprEvalCosted node add negate multiply fixed advice instanceRead left
    let b := exprEvalCosted node add negate multiply fixed advice instanceRead right
    (a.1 + b.1, a.2 + b.2 + add + node + 1)
  | .product left right =>
    let a := exprEvalCosted node add negate multiply fixed advice instanceRead left
    let b := exprEvalCosted node add negate multiply fixed advice instanceRead right
    (a.1 * b.1, a.2 + b.2 + multiply + node + 1)
  | .scaled child scalar =>
    let value := exprEvalCosted node add negate multiply fixed advice instanceRead child
    (value.1 * scalar, value.2 + multiply + node + 1)

/-- Erasing the cost reproduces the existing verifier evaluation, including all query indices. -/
theorem exprEvalCosted_result {F : Type*} [CommRing F] (node add negate multiply : ℕ)
    (fixed advice instanceRead : ℕ → F × ℕ) (expression : Expr F) :
    (exprEvalCosted node add negate multiply fixed advice instanceRead expression).1 =
      expression.eval (fun index => (fixed index).1) (fun index => (advice index).1)
        (fun index => (instanceRead index).1) := by
  induction expression <;> simp_all only [exprEvalCosted, Expr.eval]

/-- A uniform query-reader bound gives a size-linear bound on the actual evaluator. -/
theorem exprEvalCosted_cost_le {F : Type*} [CommRing F] (node add negate multiply : ℕ)
    (fixed advice instanceRead : ℕ → F × ℕ) (expression : Expr F) (access : ℕ)
    (hfixed : ∀ index, (fixed index).2 ≤ access)
    (hadvice : ∀ index, (advice index).2 ≤ access)
    (hinstance : ∀ index, (instanceRead index).2 ≤ access) :
    (exprEvalCosted node add negate multiply fixed advice instanceRead expression).2 ≤
      exprNodeCount expression * (node + 1 + access + add + negate + multiply) := by
  induction expression with
  | constant value => simp only [exprNodeCount, exprEvalCosted, Nat.one_mul]; omega
  | fixed index =>
    simp only [exprNodeCount, exprEvalCosted, Nat.one_mul]
    have h := hfixed index
    omega
  | advice index =>
    simp only [exprNodeCount, exprEvalCosted, Nat.one_mul]
    have h := hadvice index
    omega
  | «instance» index =>
    simp only [exprNodeCount, exprEvalCosted, Nat.one_mul]
    have h := hinstance index
    omega
  | negated child ih =>
    simp only [exprNodeCount, exprEvalCosted, Nat.add_mul, Nat.one_mul]
    omega
  | sum left right ihl ihr =>
    simp only [exprNodeCount, exprEvalCosted, Nat.add_mul, Nat.one_mul]
    omega
  | product left right ihl ihr =>
    simp only [exprNodeCount, exprEvalCosted, Nat.add_mul, Nat.one_mul]
    omega
  | scaled child scalar ih =>
    simp only [exprNodeCount, exprEvalCosted, Nat.add_mul, Nat.one_mul]
    omega

end Zcash.Snark.ZeroKnowledge
