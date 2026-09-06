import Zcash.Snark.Soundness.Pricing.DegreeWalk

/-!
# Separate degree bounds for lookup inputs and tables

The lookup recurrence multiplies one compressed input by one compressed table. Their
degrees add. Keeping their bounds separate matters for Orchard: the input expressions
have degree at most four, whereas the table expressions have degree at most one.
Using four for both would exceed the eight-piece quotient capacity unnecessarily.
-/

namespace Zcash.Snark.ZeroKnowledge

open CompPoly.CPolynomial

/-- Lookup constraints with separate input and table compression bounds. -/
theorem lookupExpressions_natDegree_le {B Di Dt D : ℕ}
    {fx av inst : ℕ → CPoly}
    (hfx : ∀ i, (fx i).natDegree ≤ B) (hav : ∀ i, (av i).natDegree ≤ B)
    (hinst : ∀ i, (inst i).natDegree ≤ B)
    (le : LookupEval CPoly) (inputExprs tableExprs : List (Expr Fp))
    (theta beta gamma : Fp) (l0 lLast lBlind : CPoly)
    (hle : le.productEval.natDegree ≤ B ∧ le.productNextEval.natDegree ≤ B
      ∧ le.permutedInputEval.natDegree ≤ B ∧ le.permutedInputInvEval.natDegree ≤ B
      ∧ le.permutedTableEval.natDegree ≤ B)
    (hin : ∀ e ∈ inputExprs, e.degreeBound * B ≤ Di)
    (htab : ∀ e ∈ tableExprs, e.degreeBound * B ≤ Dt)
    (hl0 : l0.natDegree ≤ B) (hll : lLast.natDegree ≤ B) (hlb : lBlind.natDegree ≤ B)
    (h4 : 4 * B ≤ D) (hcomp : 2 * B + Di + Dt ≤ D) :
    ∀ q ∈ lookupExpressions le (inputExprs.map (Expr.map C))
      (tableExprs.map (Expr.map C)) fx av inst (C theta)
      (C beta) (C gamma) l0 lLast lBlind, q.natDegree ≤ D := by
  obtain ⟨hp, hpn, hpi, hpiv, hpt⟩ := hle
  have hactive : ((1 : CPoly) - (lLast + lBlind)).natDegree ≤ B :=
    le_trans (natDegree_sub_le _ _)
      (max_le (by simp) (le_trans (natDegree_add_le _ _) (max_le hll hlb)))
  intro q hq
  simp only [lookupExpressions, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add hl0 (le_trans
      (natDegree_sub_le _ _) (max_le (by simp) hp))) (by omega))
  · have h2B : (le.productEval ^ 2 - le.productEval).natDegree ≤ 2 * B :=
      le_trans (natDegree_sub_le _ _) (max_le
        (le_trans natDegree_pow_le (Nat.mul_le_mul_left 2 hp)) (le_trans hp (by omega)))
    exact le_trans natDegree_mul_le (le_trans (Nat.add_le_add hll h2B) (by omega))
  · have hleft : (le.productNextEval * (le.permutedInputEval + C beta)
        * (le.permutedTableEval + C gamma)).natDegree ≤ 3 * B := by
      refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add (le_trans natDegree_mul_le
        (Nat.add_le_add hpn (le_trans (natDegree_add_le _ _) (max_le hpi (by simp)))))
        (le_trans (natDegree_add_le _ _) (max_le hpt (by simp)))) (by omega))
    have hright : (le.productEval
        * (compressExprs fx av inst (C theta)
            (inputExprs.map (Expr.map C)) + C beta)
        * (compressExprs fx av inst (C theta)
            (tableExprs.map (Expr.map C)) + C gamma)).natDegree
        ≤ B + Di + Dt := by
      refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add (le_trans natDegree_mul_le
        (Nat.add_le_add hp (le_trans (natDegree_add_le _ _) (max_le
          (natDegree_compressExprs_le hfx hav hinst theta inputExprs hin) (by simp)))))
        (le_trans (natDegree_add_le _ _) (max_le
          (natDegree_compressExprs_le hfx hav hinst theta tableExprs htab) (by simp))))
        (by omega))
    have hdiff := le_trans (natDegree_sub_le _ _) (max_le_max hleft hright)
    exact le_trans natDegree_mul_le (le_trans (Nat.add_le_add hdiff hactive) (by omega))
  · exact le_trans natDegree_mul_le (le_trans (Nat.add_le_add hl0 (le_trans
      (natDegree_sub_le _ _) (max_le hpi hpt))) (by omega))
  · refine le_trans natDegree_mul_le (le_trans (Nat.add_le_add (le_trans natDegree_mul_le
      (Nat.add_le_add (le_trans (natDegree_sub_le _ _) (max_le hpi hpt))
        (le_trans (natDegree_sub_le _ _) (max_le hpi hpiv)))) hactive) (by omega))

end Zcash.Snark.ZeroKnowledge
