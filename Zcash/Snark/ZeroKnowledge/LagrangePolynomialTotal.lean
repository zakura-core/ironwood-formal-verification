import Zcash.Snark.Soundness.Multiopen.RPoly

/-!
# Totalized interpolation semantics

The original indexed sum/product identity does not require distinct node values.
This version exposes that fact for real-prover execution at exceptional challenges.
Positions remain distinct indices even when their field values coincide; no node
is removed from the interpolant. The opening divisor has its separate source
point-deduplication rule.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)
open Polynomial CompPoly

/-- The original interpolation polynomial evaluates to the actual indexed loop, including repeated nodes. -/
theorem lagrangePoly_eval_total {points evals : List Fp} (x : Fp) :
    CPolynomial.eval x (lagrangePoly points evals) = lagrangeEval x points evals := by
  classical
  -- The deployed fold, as a range-indexed sum of guarded products.
  have houter : lagrangeEval x points evals
      = ∑ i ∈ Finset.range points.length, evals.getD i 0
          * ∏ j ∈ Finset.range points.length,
              if j = i then 1
              else (x - points.getD j 0) / (points.getD i 0 - points.getD j 0) := by
    show (List.range points.length).foldl (fun acc i =>
        acc + evals.getD i 0 * ((List.range points.length).foldl (fun p j =>
          if j = i then p else p * (x - points.getD j 0)
            / (points.getD i 0 - points.getD j 0)) 1)) 0 = _
    rw [foldl_range_add_eq_sum (fun i => evals.getD i 0
      * ((List.range points.length).foldl (fun p j =>
          if j = i then p else p * (x - points.getD j 0)
            / (points.getD i 0 - points.getD j 0)) 1)) points.length]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hstep : (fun (p : Fp) j => if j = i then p
        else p * (x - points.getD j 0) / (points.getD i 0 - points.getD j 0))
        = fun (p : Fp) j => if j = i then p
        else p * ((x - points.getD j 0) / (points.getD i 0 - points.getD j 0)) := by
      funext p j
      rw [mul_div_assoc]
    rw [hstep]
    exact foldl_range_guardProd_eq_prod
      (fun j => (x - points.getD j 0) / (points.getD i 0 - points.getD j 0)) i points.length
  rw [houter, ← Fin.sum_univ_eq_sum_range (fun i => evals.getD i 0
    * ∏ j ∈ Finset.range points.length,
        if j = i then 1 else (x - points.getD j 0) / (points.getD i 0 - points.getD j 0))]
  rw [CPolynomial.eval_toPoly, toPoly_lagrangePoly, Lagrange.interpolate_apply,
    eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C]
  congr 1
  rw [Lagrange.basis, eval_prod,
    ← guardProd_eq_prod_erase
      (fun j => (Lagrange.basisDivisor points[i] points[j]).eval x) i,
    ← Fin.prod_univ_eq_prod_range (fun j =>
      if j = (i : ℕ) then 1
      else (x - points.getD j 0) / (points.getD (i : ℕ) 0 - points.getD j 0))]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · simp [hj]
  · rw [if_neg hj, if_neg (fun h => hj (Fin.val_inj.mp h)),
      List.getD_eq_getElem points 0 j.isLt, List.getD_eq_getElem points 0 i.isLt,
      Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, div_eq_mul_inv,
      mul_comm]
    rfl

/-- Each indexed interpolation basis has bounded degree even when repeated nodes make it vanish. -/
theorem lagrangeBasis_natDegree_le_total (points : List Fp) (index : Fin points.length) :
    (Lagrange.basis Finset.univ (fun i : Fin points.length => points[i]) index).natDegree ≤ points.length - 1 := by
  classical
  unfold Lagrange.basis
  calc
    _ ≤ ∑ other ∈ Finset.univ.erase index,
        (Lagrange.basisDivisor points[index] points[other]).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _other ∈ Finset.univ.erase index, 1 := by
      apply Finset.sum_le_sum
      intro other _
      by_cases h : points[index] = points[other]
      · simp only [h, Lagrange.natDegree_basisDivisor_self, Nat.zero_le]
      · rewrite [Lagrange.natDegree_basisDivisor_of_ne h]
        exact le_rfl
    _ = points.length - 1 := by simp

/-- The indexed interpolant's degree bound holds without any distinctness or nonempty-list premise. -/
theorem lagrangePoly_natDegree_le_total (points evals : List Fp) :
    (lagrangePoly points evals).natDegree ≤ points.length - 1 := by
  classical
  rewrite [CPolynomial.natDegree_toPoly, toPoly_lagrangePoly, Lagrange.interpolate_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro index _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (lagrangeBasis_natDegree_le_total points index)

end Zcash.Snark.ZeroKnowledge
