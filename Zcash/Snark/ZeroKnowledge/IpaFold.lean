import Zcash.Snark.Soundness.Ipa.Halves
import Zcash.Snark.Soundness.Ipa.InnerProduct
import Mathlib.Data.Fin.Rev

/-!
# The sparse mask under the actual low/high IPA fold

The prover updates `a := a_lo + u⁻¹ a_hi`. This file uses the existing `loHalf`,
`hiHalf`, and `foldVec` definitions and proves the coefficient fold is linear. The
power-of-two coordinates select the round challenges in reverse order.

The algebra uses total field inversion. A prover execution must separately enforce its
retry policy at zero challenges; these identities do not remove that obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F : Type*} [Field F]

/-- The linear functional obtained by recursively splitting the coefficient vector. -/
def coefficientFold : (k : ℕ) → (Fin k → F) → (Fin (2 ^ k) → F) → F
  | 0, _, values => values 0
  | k + 1, rounds, values =>
      coefficientFold k (fun j => rounds j.succ) (loHalf values) +
        (rounds 0)⁻¹ * coefficientFold k (fun j => rounds j.succ) (hiHalf values)

/-- The iterative prover update, applying one fold before proceeding to the next round. -/
def foldByRounds : (k : ℕ) → (Fin k → F) → (Fin (2 ^ k) → F) → F
  | 0, _, values => values 0
  | k + 1, rounds, values =>
      foldByRounds k (fun j => rounds j.succ)
        (foldVec (loHalf values) (hiHalf values) (rounds 0)⁻¹)

/-- IPA coefficient folding preserves addition, allowing witness and mask contributions to be
analyzed separately. -/
theorem coefficientFold_add (k : ℕ) (rounds : Fin k → F)
    (left right : Fin (2 ^ k) → F) :
    coefficientFold k rounds (left + right) =
      coefficientFold k rounds left + coefficientFold k rounds right := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change coefficientFold k _ (loHalf left + loHalf right) +
        (rounds 0)⁻¹ * coefficientFold k _ (hiHalf left + hiHalf right) =
      (coefficientFold k _ (loHalf left) + (rounds 0)⁻¹ * coefficientFold k _ (hiHalf left)) +
        (coefficientFold k _ (loHalf right) + (rounds 0)⁻¹ * coefficientFold k _ (hiHalf right))
    rw [ih, ih]
    ring

/-- A scalar factor passes through IPA coefficient folding, allowing blind coefficients to be
isolated. -/
theorem coefficientFold_smul (k : ℕ) (rounds : Fin k → F)
    (scalar : F) (values : Fin (2 ^ k) → F) :
    coefficientFold k rounds (scalar • values) = scalar * coefficientFold k rounds values := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change coefficientFold k _ (scalar • loHalf values) +
        (rounds 0)⁻¹ * coefficientFold k _ (scalar • hiHalf values) =
      scalar * (coefficientFold k _ (loHalf values) +
        (rounds 0)⁻¹ * coefficientFold k _ (hiHalf values))
    rw [ih, ih]
    ring

/-- The fold as a linear map, for transporting finite sums of sparse basis vectors. -/
def coefficientFoldLinear (k : ℕ) (rounds : Fin k → F) : (Fin (2 ^ k) → F) →ₗ[F] F where
  toFun := coefficientFold k rounds
  map_add' := coefficientFold_add k rounds
  map_smul' := coefficientFold_smul k rounds

/-- A zero coefficient vector folds to zero, supplying the empty contribution in sparse-mask
calculations. -/
@[simp] theorem coefficientFold_zero (k : ℕ) (rounds : Fin k → F) :
    coefficientFold k rounds (0 : Fin (2 ^ k) → F) = 0 :=
  (coefficientFoldLinear k rounds).map_zero

/-- The linear functional is exactly the repeated update used by the prover. -/
theorem foldByRounds_eq_coefficientFold (k : ℕ) (rounds : Fin k → F)
    (values : Fin (2 ^ k) → F) :
    foldByRounds k rounds values = coefficientFold k rounds values := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [foldByRounds, ih, foldVec, coefficientFold_add, coefficientFold_smul]
    rfl

private def lowerIndex (k : ℕ) (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨i.val, by have hi := i.isLt; rw [pow_succ, Nat.mul_two]; omega⟩

private def upperIndex (k : ℕ) (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 ^ k + i.val, by have hi := i.isLt; rw [pow_succ, Nat.mul_two]; omega⟩

/-- A lower-half singleton remains a singleton after splitting, supplying the sparse-fold induction
case. -/
private theorem loHalf_single_lower (k : ℕ) (i : Fin (2 ^ k)) (value : F) :
    loHalf (Pi.single (lowerIndex k i) value) = Pi.single i value := by
  funext j
  simp [loHalf, lowerIndex, Pi.single_apply, Fin.ext_iff]

/-- An upper-half singleton remains a singleton after splitting, supplying the sparse-fold induction
case. -/
private theorem hiHalf_single_upper (k : ℕ) (i : Fin (2 ^ k)) (value : F) :
    hiHalf (Pi.single (upperIndex k i) value) = Pi.single i value := by
  funext j
  simp [hiHalf, upperIndex, Pi.single_apply, Fin.ext_iff]

/-- A lower-half singleton contributes zero to the upper half, isolating its sparse folding path. -/
private theorem hiHalf_single_lower (k : ℕ) (i : Fin (2 ^ k)) (value : F) :
    hiHalf (Pi.single (lowerIndex k i) value) = 0 := by
  funext j
  change (Pi.single (lowerIndex k i) value : Fin (2 ^ (k + 1)) → F) (upperIndex k j) = 0
  apply Pi.single_eq_of_ne
  intro heq
  have hv := congrArg Fin.val heq
  have hi := i.isLt
  change 2 ^ k + j.val = i.val at hv
  omega

/-- An upper-half singleton contributes zero to the lower half, isolating its sparse folding path. -/
private theorem loHalf_single_upper (k : ℕ) (i : Fin (2 ^ k)) (value : F) :
    loHalf (Pi.single (upperIndex k i) value) = 0 := by
  funext j
  change (Pi.single (upperIndex k i) value : Fin (2 ^ (k + 1)) → F) (lowerIndex k j) = 0
  apply Pi.single_eq_of_ne
  intro heq
  have hv := congrArg Fin.val heq
  have hj := j.isLt
  change j.val = 2 ^ k + i.val at hv
  omega

/-- A lower-half singleton folds through the remaining rounds without a first-round factor,
identifying its sparse-mask coefficient. -/
private theorem coefficientFold_single_lower (k : ℕ) (rounds : Fin (k + 1) → F)
    (i : Fin (2 ^ k)) (value : F) :
    coefficientFold (k + 1) rounds (Pi.single (lowerIndex k i) value) =
      coefficientFold k (fun j => rounds j.succ) (Pi.single i value) := by
  rw [coefficientFold, loHalf_single_lower, hiHalf_single_lower,
    coefficientFold_zero, mul_zero, add_zero]

/-- An upper-half singleton gains the inverse first challenge before folding, identifying its
sparse-mask coefficient. -/
private theorem coefficientFold_single_upper (k : ℕ) (rounds : Fin (k + 1) → F)
    (i : Fin (2 ^ k)) (value : F) :
    coefficientFold (k + 1) rounds (Pi.single (upperIndex k i) value) =
      (rounds 0)⁻¹ * coefficientFold k (fun j => rounds j.succ) (Pi.single i value) := by
  rw [coefficientFold, loHalf_single_upper, hiHalf_single_upper,
    coefficientFold_zero, zero_add]

/-- The constant coefficient is unchanged by every fold. -/
theorem coefficientFold_single_zero (k : ℕ) (rounds : Fin k → F) (value : F) :
    coefficientFold k rounds (Pi.single 0 value) = value := by
  induction k with
  | zero => simp [coefficientFold]
  | succ k ih =>
    change coefficientFold (k + 1) rounds (Pi.single (lowerIndex k 0) value) = value
    rw [coefficientFold_single_lower, ih]

/-- The coefficient index controlled by mask coordinate `t`. -/
def powerIndex {k : ℕ} (t : Fin k) : Fin (2 ^ k) :=
  ⟨2 ^ t.val, pow_lt_pow_right₀ (by decide : (1 : ℕ) < 2) t.isLt⟩

/-- Folding a power-of-two basis coefficient selects exactly one inverse round challenge. -/
theorem coefficientFold_powerIndex (k : ℕ) (rounds : Fin k → F) (t : Fin k) :
    coefficientFold k rounds (Pi.single (powerIndex t) 1) = (rounds t.rev)⁻¹ := by
  induction k with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.lastCases ?_ (fun t => ?_) t
    · change coefficientFold (k + 1) rounds (Pi.single (upperIndex k 0) 1) = _
      rw [coefficientFold_single_upper, coefficientFold_single_zero, mul_one, Fin.rev_last]
    · change coefficientFold (k + 1) rounds (Pi.single (lowerIndex k (powerIndex t)) 1) = _
      rw [coefficientFold_single_lower, ih, Fin.rev_castSucc]

/-- Evaluation of the coefficient vector as a polynomial, without a degree assumption. -/
def coefficientEvaluation (k : ℕ) (q : F) (values : Fin (2 ^ k) → F) : F :=
  ∑ i, values i * q ^ i.val

/-- Splitting a polynomial into its low and high coefficient halves. -/
theorem coefficientEvaluation_succ (k : ℕ) (q : F) (values : Fin (2 ^ (k + 1)) → F) :
    coefficientEvaluation (k + 1) q values =
      coefficientEvaluation k q (loHalf values) +
        q ^ (2 ^ k) * coefficientEvaluation k q (hiHalf values) := by
  have e : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
    finSumFinEquiv.trans (finCongr e)
  unfold coefficientEvaluation
  rw [← φ.sum_comp (fun j => values j * q ^ j.val), Fintype.sum_sum_type]
  change (∑ i, loHalf values i * q ^ i.val) +
      (∑ i, hiHalf values i * q ^ (2 ^ k + i.val)) = _
  simp_rw [pow_add]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- If every mask direction vanishes, the entire IPA fold is evaluation at `q`.

This is stronger than saying that the sparse mask disappears: a vector representing
`P + xi*s - P(q)` then folds to the publicly known scalar zero. -/
theorem coefficientFold_eq_evaluation (k : ℕ) (rounds : Fin k → F) (q : F)
    (values : Fin (2 ^ k) → F)
    (h : ∀ t : Fin k, (rounds t.rev)⁻¹ = q ^ (2 ^ t.val)) :
    coefficientFold k rounds values = coefficientEvaluation k q values := by
  induction k with
  | zero => simp [coefficientFold, coefficientEvaluation]
  | succ k ih =>
    have htail : ∀ t : Fin k,
        ((fun j => rounds j.succ) t.rev)⁻¹ = q ^ (2 ^ t.val) := by
      intro t
      simpa only [Fin.rev_castSucc, Fin.val_castSucc] using h t.castSucc
    have hhead : (rounds 0)⁻¹ = q ^ (2 ^ k) := by
      simpa only [Fin.rev_last, Fin.val_last] using h (Fin.last k)
    rw [coefficientFold, ih _ _ htail, ih _ _ htail, hhead, coefficientEvaluation_succ]

/-- The iterative prover fold has the same publicly determined evaluation case. -/
theorem foldByRounds_eq_evaluation (k : ℕ) (rounds : Fin k → F) (q : F)
    (values : Fin (2 ^ k) → F)
    (h : ∀ t : Fin k, (rounds t.rev)⁻¹ = q ^ (2 ^ t.val)) :
    foldByRounds k rounds values = coefficientEvaluation k q values := by
  rw [foldByRounds_eq_coefficientFold, coefficientFold_eq_evaluation k rounds q values h]

end Zcash.Snark.ZeroKnowledge
