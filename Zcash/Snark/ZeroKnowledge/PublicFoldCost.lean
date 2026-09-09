import Zcash.Snark.ZeroKnowledge.IpaProver

/-!
# Counted public IPA folding

The counted fold executes the same group expressions as `publicFold`. Its input
readers return values with their complete access costs. Every recursive case,
index adapter, dimension calculation, and group operation contributes to the
counter. The caller supplies prices for group addition and scalar multiplication;
those prices must cover the chosen representations and primitive algorithms.

Natural-number arithmetic is priced as bounded-width index arithmetic. At the
Action protocol's eleven rounds the largest vector dimension is 2048. This is a
structural cost model, not a correspondence with Lean-generated machine code.
The theorem bounds a completed fold result. It neither prices unrelated public
input preparation nor treats a function-valued transcript as materialized output.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Compute the half-vector dimension, charging a case test and doubling at each successor. -/
def powTwoCosted : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => let previous := powTwoCosted n; (previous.1 * 2, previous.2 + 2)

/-- The counted dimension is exactly the dimension used by the existing IPA index adapter. -/
theorem powTwoCosted_result (n : ℕ) : (powTwoCosted n).1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [powTwoCosted, pow_succ] using congrArg (· * 2) ih

/-- Exact structural cost of computing the dimension. -/
theorem powTwoCosted_cost (n : ℕ) : (powTwoCosted n).2 = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powTwoCosted, ih]; omega

/-- The lower read retains the supplied reader's complete cost and charges its index adapter. -/
def loHalfCosted {α : Type*} {k : ℕ} (read : Fin (2 ^ (k + 1)) → α × ℕ) (index : Fin (2 ^ k)) : α × ℕ :=
  let value := loHalf read index
  (value.1, value.2 + 1)

/-- The upper read explicitly computes its dimension and offset before invoking the supplied reader. -/
def hiHalfCosted {α : Type*} {k : ℕ} (read : Fin (2 ^ (k + 1)) → α × ℕ) (index : Fin (2 ^ k)) : α × ℕ :=
  let width := powTwoCosted k
  let value := read ⟨width.1 + index.val, by
    have hwidth := powTwoCosted_result k
    have hindex := index.isLt
    dsimp only [width]
    rw [hwidth, pow_succ]
    omega⟩
  (value.1, value.2 + width.2 + 2)

/-- Cost erasure retains the original lower-half read. -/
theorem loHalfCosted_result {α : Type*} {k : ℕ}
    (read : Fin (2 ^ (k + 1)) → α × ℕ) (index : Fin (2 ^ k)) :
    (loHalfCosted read index).1 = loHalf (fun i => (read i).1) index := rfl

/-- Cost erasure retains the original upper-half read. -/
theorem hiHalfCosted_result {α : Type*} {k : ℕ}
    (read : Fin (2 ^ (k + 1)) → α × ℕ) (index : Fin (2 ^ k)) :
    (hiHalfCosted read index).1 = hiHalf (fun i => (read i).1) index := by
  simp only [hiHalfCosted, hiHalf, powTwoCosted_result]

/-- Lower-half access is bounded by the complete supplied reader cost. -/
theorem loHalfCosted_cost_le {α : Type*} {k : ℕ}
    (read : Fin (2 ^ (k + 1)) → α × ℕ) (bound : ℕ)
    (hread : ∀ index, (read index).2 ≤ bound) (index : Fin (2 ^ k)) :
    (loHalfCosted read index).2 ≤ bound + 1 :=
  Nat.add_le_add_right (hread _) 1

/-- Upper-half access also pays for its dimension computation and offset. -/
theorem hiHalfCosted_cost_le {α : Type*} {k : ℕ}
    (read : Fin (2 ^ (k + 1)) → α × ℕ) (bound : ℕ)
    (hread : ∀ index, (read index).2 ≤ bound) (index : Fin (2 ^ k)) :
    (hiHalfCosted read index).2 ≤ bound + 2 * k + 3 := by
  unfold hiHalfCosted
  simp only [powTwoCosted_cost]
  have h := hread ⟨(powTwoCosted k).1 + index.val, by
    rw [powTwoCosted_result, pow_succ]
    have hi := index.isLt
    omega⟩
  omega

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Count the existing public fold, including supplied readers, index arithmetic, and every group operation. -/
def publicFoldCosted (addCost scaleCost : ℕ) :
    (k : ℕ) → (Fin k → F × ℕ) → (Fin (2 ^ k) → G × ℕ) → G × ℕ
  | 0, _, values => let value := values 0; (value.1, value.2 + 1)
  | k + 1, rounds, values =>
    let result := publicFoldCosted addCost scaleCost k
      (fun index => let challenge := rounds index.succ; (challenge.1, challenge.2 + 1))
      (fun index =>
        let low := loHalfCosted values index
        let high := hiHalfCosted values index
        let challenge := rounds 0
        (low.1 + challenge.1 • high.1, low.2 + high.2 + challenge.2 + addCost + scaleCost + 1))
    (result.1, result.2 + 1)

/-- Erasing all costs yields precisely the existing public IPA fold. -/
theorem publicFoldCosted_result (addCost scaleCost k : ℕ)
    (rounds : Fin k → F × ℕ) (values : Fin (2 ^ k) → G × ℕ) :
    (publicFoldCosted addCost scaleCost k rounds values).1 =
      publicFold k (fun index => (rounds index).1) (fun index => (values index).1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [publicFoldCosted, ih, publicFold]
    congr 1
    funext index
    simp only [loHalfCosted_result, hiHalfCosted_result, Pi.add_apply, Pi.smul_apply]

/-- A complete reader bound gives a concrete bound on the actual counted public fold. -/
theorem publicFoldCosted_cost_le (addCost scaleCost k : ℕ)
    (rounds : Fin k → F × ℕ) (values : Fin (2 ^ k) → G × ℕ) (roundRead valueRead : ℕ)
    (hround : ∀ index, (rounds index).2 ≤ roundRead)
    (hvalue : ∀ index, (values index).2 ≤ valueRead) :
    (publicFoldCosted addCost scaleCost k rounds values).2 ≤
      2 ^ k * (valueRead + k * (roundRead + 2 * k + addCost + scaleCost + 10)) + k + 1 := by
  induction k generalizing roundRead valueRead with
  | zero => simpa only [publicFoldCosted, pow_zero, Nat.zero_mul, Nat.add_zero, Nat.one_mul]
      using Nat.add_le_add_right (hvalue 0) 1
  | succ k ih =>
    have hnext (index : Fin (2 ^ k)) :
        (loHalfCosted values index).2 + (hiHalfCosted values index).2 + (rounds 0).2 +
          addCost + scaleCost + 1 ≤ 2 * valueRead + roundRead + addCost + scaleCost + 2 * k + 5 := by
      have hl := loHalfCosted_cost_le values valueRead hvalue index
      have hh := hiHalfCosted_cost_le values valueRead hvalue index
      have hr := hround 0
      omega
    have hfold := ih
      (fun index => ((rounds index.succ).1, (rounds index.succ).2 + 1))
      (fun index =>
        ((loHalfCosted values index).1 + (rounds 0).1 • (hiHalfCosted values index).1,
          (loHalfCosted values index).2 + (hiHalfCosted values index).2 + (rounds 0).2 +
            addCost + scaleCost + 1))
      (roundRead + 1) (2 * valueRead + roundRead + addCost + scaleCost + 2 * k + 5)
      (fun index => Nat.add_le_add_right (hround index.succ) 1) hnext
    have hinner :
        (2 * valueRead + roundRead + addCost + scaleCost + 2 * k + 5) +
          k * (roundRead + 1 + 2 * k + addCost + scaleCost + 10) ≤
        2 * (valueRead + (k + 1) * (roundRead + 2 * (k + 1) + addCost + scaleCost + 10)) := by
      nlinarith
    change (publicFoldCosted addCost scaleCost k _ _).2 + 1 ≤ _
    calc
      _ ≤ (2 ^ k * ((2 * valueRead + roundRead + addCost + scaleCost + 2 * k + 5) +
          k * (roundRead + 1 + 2 * k + addCost + scaleCost + 10)) + k + 1) + 1 :=
        Nat.add_le_add_right hfold 1
      _ ≤ 2 ^ k * (2 * (valueRead + (k + 1) *
          (roundRead + 2 * (k + 1) + addCost + scaleCost + 10))) + (k + 1) + 1 := by
        have h := Nat.mul_le_mul_left (2 ^ k) hinner
        omega
      _ = _ := by rw [pow_succ]; ring

end Zcash.Snark.ZeroKnowledge
