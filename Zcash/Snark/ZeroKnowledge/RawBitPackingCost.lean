import Zcash.Snark.ZeroKnowledge.RawBits

/-!
# Counted little-endian bit packing

The input reader returns both a bit and its complete access cost. One unit is
charged for each recursive case test, Boolean branch, doubling, and addition;
each successor-index adapter also adds one unit to the reader's cost. Thus an
arbitrary supplied reader is not treated as free, including the chain of index
adapters built by recursion.

At width 512 every intermediate integer fits in 512 bits. Arithmetic units in
this component are bounded-width operations, not a claim about the execution
time of Lean's arbitrary-precision implementation. The caller must supply a
costed input representation. Field reduction and later simulator work are
separate components.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Pack low bits first, retaining input-access and structural operation costs. -/
def packBitsLECosted : {width : ℕ} → (Fin width → Bool × ℕ) → ℕ × ℕ
  | 0, _ => (0, 1)
  | width + 1, read =>
    let upper := packBitsLECosted (width := width) fun index =>
      let bit := read index.succ
      (bit.1, bit.2 + 1)
    let lower := read 0
    ((if lower.1 then 1 else 0) + 2 * upper.1, upper.2 + lower.2 + 4)

/-- Erasing costs gives the exact little-endian value, for every input reader. -/
theorem packBitsLECosted_result {width : ℕ} (read : Fin width → Bool × ℕ) :
    (packBitsLECosted read).1 =
      ∑ bit : Fin width, (if (read bit).1 then 1 else 0) * 2 ^ bit.val := by
  induction width with
  | zero => simp [packBitsLECosted]
  | succ width ih =>
    rw [Fin.sum_univ_succ]
    simp only [packBitsLECosted, ih, Fin.val_zero, pow_zero, mul_one,
      Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro bit _
    ring

/-- The counted algorithm never constructs an integer outside its bit width. -/
theorem packBitsLECosted_lt {width : ℕ} (read : Fin width → Bool × ℕ) :
    (packBitsLECosted read).1 < 2 ^ width := by
  induction width with
  | zero => simp [packBitsLECosted]
  | succ width ih =>
    have upper := ih (fun index => ((read index.succ).1, (read index.succ).2 + 1))
    simp only [packBitsLECosted, pow_succ]
    split <;> omega

/-- A bound on complete reader accesses gives a uniform structural packing bound. -/
theorem packBitsLECosted_cost_le {width : ℕ} (read : Fin width → Bool × ℕ)
    (access : ℕ) (haccess : ∀ bit, (read bit).2 ≤ access) :
    (packBitsLECosted read).2 ≤ width * (access + 4) + width * width + 1 := by
  induction width generalizing access with
  | zero => simp [packBitsLECosted]
  | succ width ih =>
    have upper := ih (fun index => ((read index.succ).1, (read index.succ).2 + 1))
      (access + 1) (fun index => Nat.add_le_add_right (haccess index.succ) 1)
    have lower := haccess 0
    simp only [packBitsLECosted]
    nlinarith

/-- The counted 512-bit packer is exactly the existing raw tape's word encoding. -/
theorem packBitsLECosted_raw_word {count : ℕ}
    (bits : Fin (count * 512) → Bool) (access : Fin (count * 512) → ℕ)
    (word : Fin count) :
    (packBitsLECosted (fun bit : Fin 512 =>
      (bits (finProdFinEquiv (word, bit)), access (finProdFinEquiv (word, bit))))).1 =
      (rawBitsTapeEquiv count bits word).val := by
  rw [packBitsLECosted_result, rawBitsTapeEquiv_word]
  apply Finset.sum_congr rfl
  intro bit _
  cases bits (finProdFinEquiv (word, bit)) <;> rfl

/-- A raw 512-bit word has a fixed packing bound plus the charged bit accesses. -/
theorem packBitsLECosted_raw_word_cost_le {count : ℕ}
    (bits : Fin (count * 512) → Bool) (access : Fin (count * 512) → ℕ)
    (bound : ℕ) (haccess : ∀ bit, access bit ≤ bound) (word : Fin count) :
    (packBitsLECosted (fun bit : Fin 512 =>
      (bits (finProdFinEquiv (word, bit)), access (finProdFinEquiv (word, bit))))).2 ≤
      512 * bound + 264193 := by
  have cost := packBitsLECosted_cost_le (fun bit : Fin 512 =>
    (bits (finProdFinEquiv (word, bit)), access (finProdFinEquiv (word, bit))))
    bound (fun bit => haccess (finProdFinEquiv (word, bit)))
  omega

end Zcash.Snark.ZeroKnowledge
