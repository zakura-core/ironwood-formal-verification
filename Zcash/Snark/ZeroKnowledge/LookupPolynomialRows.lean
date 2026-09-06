import Zcash.Snark.ZeroKnowledge.PlonkSelectorRows
import Zcash.Snark.ZeroKnowledge.DomainDivisibility
import Zcash.Snark.Soundness.Canonical.LookupRows

/-!
# From lookup scans to the actual polynomial constraints

Evaluation commutes with the existing lookup builder, including expression constants
and rotated columns. The row-scan correctness theorem therefore makes each of its five
polynomials vanish on the domain and gives exact divisibility by the domain polynomial.
The construction premises describe compression, sorting, and the computed product scan;
no constraint-vanishing or quotient-identity premise is assumed.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open CompPoly.CPolynomial

/-- Evaluating the polynomial builder recovers the same scalar constraint builder. -/
theorem lookupExpressions_polynomial_eval
    (le : LookupEval CPoly) (inputExprs tableExprs : List (Expr Fp))
    (fixed advice instanceCols : ℕ → CPoly) (theta beta gamma : Fp)
    (l0 lLast lBlind : CPoly) (x : Fp) :
    (lookupExpressions le (inputExprs.map (Expr.map C)) (tableExprs.map (Expr.map C))
      fixed advice instanceCols (C theta) (C beta) (C gamma) l0 lLast lBlind).map
        (fun poly => poly.eval x) =
    lookupExpressions (le.map (fun poly => poly.eval x)) inputExprs tableExprs
      (fun j => (fixed j).eval x) (fun j => (advice j).eval x) (fun j => (instanceCols j).eval x)
      theta beta gamma (l0.eval x) (lLast.eval x) (lBlind.eval x) := by
  have h := lookupExpressions_map (evalRingHom x) le (inputExprs.map (Expr.map C))
    (tableExprs.map (Expr.map C)) fixed advice instanceCols (C theta) (C beta) (C gamma)
    l0 lLast lBlind
  simp only [coe_evalRingHom, eval_C] at h
  rw [h, List.map_map, List.map_map]
  have hid (e : Expr Fp) :
      (Expr.map (fun poly : CPoly => poly.eval x) ∘ Expr.map C) e = e := by
    simp only [Function.comp_apply, Expr.map_map, eval_C]
    exact Expr.map_id e
  have hfun : Expr.map (fun poly : CPoly => poly.eval x) ∘ Expr.map C = id := funext hid
  rw [hfun, List.map_id, List.map_id]

/-- Actual rotated polynomial constraints vanish at a row by the computed scan's row rules. -/
theorem lookupExpressions_eval_row_zero_of_scan
    (omega : Fp) (homega : omega ≠ 0) (usable row : ℕ)
    (input table : ℕ → Fp) (z b t : CPoly)
    (inputExprs tableExprs : List (Expr Fp))
    (fixed advice instanceCols : ℕ → CPoly) (theta beta gamma : Fp)
    (selectors : CPoly × CPoly × CPoly)
    (hselectors : (selectors.1.eval (omega ^ row), selectors.2.1.eval (omega ^ row),
      selectors.2.2.eval (omega ^ row)) = rowSelectorValues (F := Fp) usable row)
    (hinput : ∀ i < usable, compressExprs (fun j => (fixed j).eval (omega ^ i))
      (fun j => (advice j).eval (omega ^ i)) (fun j => (instanceCols j).eval (omega ^ i))
      theta inputExprs = input i)
    (htable : ∀ i < usable, compressExprs (fun j => (fixed j).eval (omega ^ i))
      (fun j => (advice j).eval (omega ^ i)) (fun j => (instanceCols j).eval (omega ^ i))
      theta tableExprs = table i)
    (hz : ∀ i ≤ usable, z.eval (omega ^ i) = lookupProductRows input table
      (fun j => b.eval (omega ^ j)) (fun j => t.eval (omega ^ j)) beta gamma i)
    (hinputPerm : (List.ofFn fun i : Fin usable => input i.val).Perm
      (List.ofFn fun i : Fin usable => b.eval (omega ^ i.val)))
    (htablePerm : (List.ofFn fun i : Fin usable => table i.val).Perm
      (List.ofFn fun i : Fin usable => t.eval (omega ^ i.val)))
    (hfirst : b.eval (omega ^ 0) = t.eval (omega ^ 0))
    (hrun : ∀ i, 0 < i → i < usable →
      b.eval (omega ^ i) = t.eval (omega ^ i) ∨ b.eval (omega ^ i) = b.eval (omega ^ (i - 1)))
    (hden : ∀ i < usable, b.eval (omega ^ i) + beta ≠ 0 ∧ t.eval (omega ^ i) + gamma ≠ 0) :
    (lookupExpressions (lookupEvalPolys omega z b t)
      (inputExprs.map (Expr.map C)) (tableExprs.map (Expr.map C))
      fixed advice instanceCols (C theta) (C beta) (C gamma)
      selectors.1 selectors.2.1 selectors.2.2).map (fun poly => poly.eval (omega ^ row)) =
        List.replicate 5 0 := by
  have h0 := congrArg Prod.fst hselectors
  have hlast := congrArg (fun s : Fp × Fp × Fp => s.2.1) hselectors
  have hblind := congrArg (fun s : Fp × Fp × Fp => s.2.2) hselectors
  dsimp only at h0 hlast hblind
  rw [lookupExpressions_polynomial_eval, h0, hlast, hblind]
  apply lookupExpressions_zero_of_scan input table
    (fun i => b.eval (omega ^ i)) (fun i => t.eval (omega ^ i))
    (fun i => z.eval (omega ^ i))
    (fun i => (lookupEvalPolys omega z b t).productNextEval.eval (omega ^ i))
    (fun i => (lookupEvalPolys omega z b t).permutedInputInvEval.eval (omega ^ i))
    inputExprs tableExprs
    (fun i j => (fixed j).eval (omega ^ i)) (fun i j => (advice j).eval (omega ^ i))
    (fun i j => (instanceCols j).eval (omega ^ i)) theta beta gamma usable row
    hinput htable hz ?_ ?_ hinputPerm htablePerm hfirst hrun hden
  · intro i _
    exact eval_lookupEvalPolys_productNextEval omega z b t i
  · intro i hi _
    have hi' : i - 1 + 1 = i := by omega
    simpa only [hi'] using eval_lookupEvalPolys_permutedInputInvEval_succ omega z b t homega (i - 1)

/-- The computed lookup scan supplies exact domain division for all five constraint polynomials. -/
theorem lookupExpressions_dvd_domain_of_scan
    {n : ℕ} (omega : Fp) (hn : 0 < n) (hroot : IsPrimitiveRoot omega n) (usable : ℕ)
    (input table : ℕ → Fp) (z b t : CPoly)
    (inputExprs tableExprs : List (Expr Fp))
    (fixed advice instanceCols : ℕ → CPoly) (theta beta gamma : Fp)
    (selectors : CPoly × CPoly × CPoly)
    (hselectors : ∀ row : Fin n,
      (selectors.1.eval (omega ^ row.val), selectors.2.1.eval (omega ^ row.val),
        selectors.2.2.eval (omega ^ row.val)) = rowSelectorValues (F := Fp) usable row.val)
    (hinput : ∀ i < usable, compressExprs (fun j => (fixed j).eval (omega ^ i))
      (fun j => (advice j).eval (omega ^ i)) (fun j => (instanceCols j).eval (omega ^ i))
      theta inputExprs = input i)
    (htable : ∀ i < usable, compressExprs (fun j => (fixed j).eval (omega ^ i))
      (fun j => (advice j).eval (omega ^ i)) (fun j => (instanceCols j).eval (omega ^ i))
      theta tableExprs = table i)
    (hz : ∀ i ≤ usable, z.eval (omega ^ i) = lookupProductRows input table
      (fun j => b.eval (omega ^ j)) (fun j => t.eval (omega ^ j)) beta gamma i)
    (hinputPerm : (List.ofFn fun i : Fin usable => input i.val).Perm
      (List.ofFn fun i : Fin usable => b.eval (omega ^ i.val)))
    (htablePerm : (List.ofFn fun i : Fin usable => table i.val).Perm
      (List.ofFn fun i : Fin usable => t.eval (omega ^ i.val)))
    (hfirst : b.eval (omega ^ 0) = t.eval (omega ^ 0))
    (hrun : ∀ i, 0 < i → i < usable →
      b.eval (omega ^ i) = t.eval (omega ^ i) ∨ b.eval (omega ^ i) = b.eval (omega ^ (i - 1)))
    (hden : ∀ i < usable, b.eval (omega ^ i) + beta ≠ 0 ∧ t.eval (omega ^ i) + gamma ≠ 0) :
    ∀ poly ∈ lookupExpressions (lookupEvalPolys omega z b t)
      (inputExprs.map (Expr.map C)) (tableExprs.map (Expr.map C))
      fixed advice instanceCols (C theta) (C beta) (C gamma)
      selectors.1 selectors.2.1 selectors.2.2, (X ^ n - 1 : CPoly) ∣ poly := by
  intro poly hpoly
  apply domainPolynomial_dvd_of_rows omega hn hroot poly
  intro row
  have hzero := lookupExpressions_eval_row_zero_of_scan omega (hroot.ne_zero hn.ne')
    usable row.val input table z b t inputExprs tableExprs fixed advice instanceCols
    theta beta gamma selectors (hselectors row) hinput htable hz hinputPerm htablePerm hfirst hrun hden
  have hmem := List.mem_map_of_mem (f := fun q : CPoly => q.eval (omega ^ row.val)) hpoly
  rw [hzero] at hmem
  exact List.eq_of_mem_replicate hmem

end Zcash.Snark.ZeroKnowledge
