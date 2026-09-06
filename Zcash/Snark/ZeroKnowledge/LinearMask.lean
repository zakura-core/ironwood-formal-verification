import Zcash.Common.UniformMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The two evaluations of the linear multi-opening mask

The pinned prover uses `r(X) = a + b X`: `r(x)` is emitted, and `r(q)` contributes
to the later aggregate opening. For distinct points and independent uniform coefficients,
the joint pair is uniform. This lemma includes the first, already disclosed evaluation;
uniformity of the second marginal alone would not establish that it masks anything.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F : Type*} [Field F]

/-- Evaluations of the linear polynomial with coefficients `(a, b)`. -/
def linearMaskPair (x q : F) (coefficients : F × F) : F × F :=
  (coefficients.1 + coefficients.2 * x, coefficients.1 + coefficients.2 * q)

/-- Recovering the coefficients from two distinct evaluations is an explicit bijection. -/
def linearMaskEquiv (x q : F) (h : q ≠ x) : (F × F) ≃ (F × F) where
  toFun := linearMaskPair x q
  invFun := fun values =>
    (values.1 - (values.2 - values.1) / (q - x) * x,
      (values.2 - values.1) / (q - x))
  left_inv := by
    intro coefficients
    have hne : q - x ≠ 0 := sub_ne_zero.mpr h
    apply Prod.ext <;> simp only [linearMaskPair] <;> field_simp <;> ring
  right_inv := by
    intro values
    have hne : q - x ≠ 0 := sub_ne_zero.mpr h
    apply Prod.ext <;> simp only [linearMaskPair] <;> field_simp <;> ring

/-- Perfect joint hiding by the ideal linear mask, explicitly conditional on distinct points. -/
theorem linearMaskPair_uniform [Fintype F] (x q : F) (h : q ≠ x) :
    (PMF.uniformOfFintype (F × F)).map (linearMaskPair x q) =
      PMF.uniformOfFintype (F × F) :=
  Zcash.map_uniformOfFintype_equiv (linearMaskEquiv x q h)

/-- Adding any function of the disclosed first value to the second value is reversible. -/
def addSecondEquiv (offset : F → F) : (F × F) ≃ (F × F) where
  toFun := fun values => (values.1, offset values.1 + values.2)
  invFun := fun values => (values.1, values.2 - offset values.1)
  left_inv := by intro values; apply Prod.ext <;> simp
  right_inv := by intro values; apply Prod.ext <;> simp

/-- The verifier sees `r(x)` and the later group evaluation with `r(q)` added at unit weight. -/
def linearMaskView (x q : F) (offset : F → F) (coefficients : F × F) : F × F :=
  addSecondEquiv offset (linearMaskPair x q coefficients)

/-- The pair remains uniform after masking a later value that may depend on `r(x)`.

There is no nonzero batching-challenge premise: the last polynomial's Horner coefficient is
one. Relating the complete group construction and earlier commitments to these inputs is
an additional protocol obligation. -/
theorem linearMaskView_uniform [Fintype F] (x q : F) (offset : F → F) (h : q ≠ x) :
    (PMF.uniformOfFintype (F × F)).map (linearMaskView x q offset) =
      PMF.uniformOfFintype (F × F) :=
  Zcash.map_uniformOfFintype_equiv ((linearMaskEquiv x q h).trans (addSecondEquiv offset))

/-- Appending the mask to a Horner fold gives it coefficient one, including at challenge zero. -/
theorem horner_last_unit_weight (challenge : F) (earlier : List F) (mask : F) :
    (earlier ++ [mask]).foldl (fun acc value => acc * challenge + value) 0 =
      earlier.foldl (fun acc value => acc * challenge + value) 0 * challenge + mask := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- With zero batching challenge the appended mask is exactly the aggregate. -/
theorem horner_last_at_zero (earlier : List F) (mask : F) :
    (earlier ++ [mask]).foldl (fun acc value => acc * 0 + value) 0 = mask := by
  rw [horner_last_unit_weight]
  simp

end Zcash.Snark.ZeroKnowledge
