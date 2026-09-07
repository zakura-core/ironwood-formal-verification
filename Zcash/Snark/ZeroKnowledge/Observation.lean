import Zcash.Snark.ZeroKnowledge.Domain
import Zcash.Snark.ZeroKnowledge.Randomness

/-!
# Distribution of a disclosed domain-row evaluation

An interactive verifier's view includes its challenge as well as the scalar it receives.
When the challenge is a domain point at an unmasked row, the scalar equals that witness
cell with probability one, regardless of the law of the masks. This module computes the
probability of that joint observation, instead of arguing only about a scalar marginal.

The resulting distinction is between column-opening views of different row vectors.
An end-to-end impossibility claim additionally needs two satisfying witnesses for the
same public statement and a proof that the full execution exposes this observation.
In particular, reaching this stage, aborts, retries, and conditioning cannot be omitted.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)

/-- A fresh independent challenge and its emitted evaluation, retaining both in the view. -/
noncomputable def evaluationView {F R : Type*} (challengeLaw : PMF F) (maskLaw : PMF R)
    (evaluate : R → F → F) : PMF (F × F) :=
  challengeLaw.bind fun x => maskLaw.map fun mask => (x, evaluate mask x)

/-- Exact observation mass for a challenge-dependent computation that discloses a fixed cell.

Only the selected challenge coordinate is retained by this projection. The other
coins may change the computation and its private distribution arbitrarily. -/
theorem projectedKernelView_apply_at_point {C A F : Type*} [DecidableEq F]
    (law : PMF C) (run : C → PMF A) (challenge : C → F) (observe : A → F)
    (point cell value : F)
    (hcell : ∀ c, challenge c = point → (run c).map observe = PMF.pure cell) :
    (law.bind fun c => (run c).map fun a => (challenge c, observe a)) (point, value) =
      if value = cell then (law.map challenge) point else 0 := by
  classical
  have hkernel (c : C) :
      ((run c).map fun a => (challenge c, observe a)) (point, value) =
        if point = challenge c then (if value = cell then 1 else 0) else 0 := by
    by_cases hx : point = challenge c
    · have hmap : (run c).map (fun a => (challenge c, observe a)) =
          ((run c).map observe).map (Prod.mk (challenge c)) :=
        (PMF.map_comp _ _ _).symm
      rw [hmap, hcell c hx.symm, PMF.pure_map]
      simp [PMF.pure_apply, hx]
    · simp [PMF.map_apply, hx]
  rw [PMF.bind_apply]
  by_cases hv : value = cell
  · rw [if_pos hv, PMF.map_apply]
    apply tsum_congr
    intro c
    rw [hkernel]
    by_cases hx : point = challenge c <;> simp [hx, hv]
  · rw [if_neg hv]
    simp [hkernel, hv]

/-- Exact mass of a joint observation when every mask gives the same value at that point. -/
theorem evaluationView_apply_at_point {F R : Type*} [DecidableEq F]
    (challengeLaw : PMF F) (maskLaw : PMF R)
    (evaluate : R → F → F) (point cell value : F)
    (hcell : ∀ mask, evaluate mask point = cell) :
    evaluationView challengeLaw maskLaw evaluate (point, value) =
      if value = cell then challengeLaw point else 0 := by
  classical
  have hfixed : maskLaw.map (fun mask => (point, evaluate mask point)) =
      PMF.pure (point, cell) := by
    simp_rw [hcell]
    exact PMF.map_const maskLaw (point, cell)
  rw [evaluationView, PMF.bind_apply,
    tsum_eq_single point (fun other hother => ?_), hfixed]
  · simp [PMF.pure_apply, mul_ite]
  · simp [PMF.map_apply, Ne.symm hother]

/-- Distinct disclosed cells give distinct joint distributions whenever the point is possible. -/
theorem evaluationView_ne_of_disclosed_cell {F R : Type*}
    (challengeLaw : PMF F) (maskLaw : PMF R) (left right : R → F → F)
    (point a b : F) (hleft : ∀ mask, left mask point = a)
    (hright : ∀ mask, right mask point = b) (hab : a ≠ b)
    (hpoint : challengeLaw point ≠ 0) :
    evaluationView challengeLaw maskLaw left ≠ evaluationView challengeLaw maskLaw right := by
  classical
  intro heq
  have hmass := congrArg (fun law : PMF (F × F) => law (point, a)) heq
  change evaluationView challengeLaw maskLaw left (point, a) =
    evaluationView challengeLaw maskLaw right (point, a) at hmass
  rw [evaluationView_apply_at_point challengeLaw maskLaw left point a a hleft,
    evaluationView_apply_at_point challengeLaw maskLaw right point b a hright,
    if_pos rfl, if_neg hab] at hmass
  exact hpoint hmass

/-- The precise advice evaluation projection of step 5 in the pinned description. -/
noncomputable def adviceEvaluationView (challengeLaw : PMF Fp)
    (maskLaw : PMF (RowMask 2048 2042)) (witness : Fin 2048 → Fp) : PMF (Fp × Fp) :=
  evaluationView challengeLaw maskLaw fun mask x => (advicePolynomial witness mask).eval x

/-- Masking the six suffix rows cannot identify the distributions of different usable cells. -/
theorem adviceEvaluationView_ne_of_usable_cell (challengeLaw : PMF Fp)
    (maskLaw : PMF (RowMask 2048 2042)) (left right : Fin 2048 → Fp)
    (i : Fin 2048) (hi : i.val < 2042) (hcell : left i ≠ right i)
    (hpoint : challengeLaw ((omegaOf 11) ^ i.val) ≠ 0) :
    adviceEvaluationView challengeLaw maskLaw left ≠
      adviceEvaluationView challengeLaw maskLaw right :=
  evaluationView_ne_of_disclosed_cell challengeLaw maskLaw _ _
    ((omegaOf 11) ^ i.val) (left i) (right i)
    (fun mask => advicePolynomial_eval_usable left mask i hi)
    (fun mask => advicePolynomial_eval_usable right mask i hi) hcell hpoint

/-- The exceptional observation still has positive probability under the implemented field law. -/
theorem adviceEvaluationView_ne_under_wide_reduction
    (maskLaw : PMF (RowMask 2048 2042)) (left right : Fin 2048 → Fp)
    (i : Fin 2048) (hi : i.val < 2042) (hcell : left i ≠ right i) :
    adviceEvaluationView fieldSample maskLaw left ≠
      adviceEvaluationView fieldSample maskLaw right :=
  adviceEvaluationView_ne_of_usable_cell fieldSample maskLaw left right i hi hcell
    (fieldSample_ne_zero _)

end Zcash.Snark.ZeroKnowledge
