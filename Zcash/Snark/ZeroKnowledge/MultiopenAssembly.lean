import Zcash.Snark.Soundness.Multiopen.Deployed

/-!
# Semantic congruence of the final multi-opening combination

The commitment accumulator depends on each input MSM only through its evaluated
group point. The scalar accumulator depends on the same ordered quotient values.
Thus two representations of the compressed commitments give the same opening.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Msm Msm.zero URS)

section Combine

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

private theorem combineFold_evaluated (urs : URS G) (x4 : F)
    (pairs : List (Msm urs.k F G × F)) (state : Msm urs.k F G × F) :
    let result := pairs.foldl
      (fun state pair => ((state.1.scale x4).add pair.1, state.2 * x4 + pair.2)) state
    (result.1.eval urs, result.2) =
      (pairs.map (fun pair => (pair.1.eval urs, pair.2))).foldl
        (fun state pair => (x4 • state.1 + pair.1, state.2 * x4 + pair.2)) (state.1.eval urs, state.2) := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair pairs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp only [Msm.eval_add, Msm.eval_scale]

/-- Evaluate the final MSM/scalar pair by folding only group points and scalar claims. -/
theorem multiopenCombine_evaluated (urs : URS G) (x4 : F) (qPrime : G)
    (commitments : List (Msm urs.k F G)) (values : List F) (base : F) :
    let result := multiopenCombine x4 qPrime commitments values base (Msm.zero urs.k F G)
    (result.1.eval urs, result.2) =
      ((commitments.map (fun msm => msm.eval urs)).zip values).foldl
        (fun state pair => (x4 • state.1 + pair.1, state.2 * x4 + pair.2)) (qPrime, base) := by
  have h := combineFold_evaluated urs x4 (commitments.zip values)
    ((Msm.zero urs.k F G).appendTerm 1 qPrime, base)
  simpa only [multiopenCombine, List.zip_map_left, Msm.eval_appendTerm, Msm.eval_zero,
    one_smul, zero_add] using h

/-- Equal evaluated commitment lists give exactly the same final opening point and scalar. -/
theorem multiopenCombine_evaluated_congr (urs : URS G) (x4 : F) (qPrime : G)
    (left right : List (Msm urs.k F G))
    (hcommitments : left.map (fun msm => msm.eval urs) = right.map (fun msm => msm.eval urs))
    (values : List F) (base : F) :
    let lhs := multiopenCombine x4 qPrime left values base (Msm.zero urs.k F G)
    let rhs := multiopenCombine x4 qPrime right values base (Msm.zero urs.k F G)
    (lhs.1.eval urs, lhs.2) = (rhs.1.eval urs, rhs.2) := by
  refine (multiopenCombine_evaluated urs x4 qPrime left values base).trans ?_
  rw [hcommitments]
  exact (multiopenCombine_evaluated urs x4 qPrime right values base).symm

end Combine

end Zcash.Snark.ZeroKnowledge
