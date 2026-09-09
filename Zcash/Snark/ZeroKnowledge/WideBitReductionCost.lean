import Zcash.Snark.ZeroKnowledge.RawBitPackingCost

/-!
# Counted wide reduction directly from input bits

Horner evaluation in the fixed Pasta field has exactly the same result as
packing the input integer and reducing it modulo the field order. This variant
charges field additions explicitly: one unit each for doubling and adding the
low bit, plus the case test, Boolean branch, and complete reader costs already
used by the bit packer. Every field operand has the fixed field width.

These are structural field-operation units. Translating them to machine time
requires the stated bounded-width primitive implementation, and using this
component in the complete simulator still requires a composition proof.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Reduce low bits first, charging both fixed-field additions and all bit accesses. -/
def wideReduceBitsLECosted : {width : ℕ} → (Fin width → Bool × ℕ) → Fp × ℕ
  | 0, _ => (0, 1)
  | width + 1, read =>
    let upper := wideReduceBitsLECosted (width := width) fun index =>
      let bit := read index.succ
      (bit.1, bit.2 + 1)
    let lower := read 0
    ((if lower.1 then 1 else 0) + (upper.1 + upper.1), upper.2 + lower.2 + 4)

/-- Direct field Horner evaluation is exactly packing followed by the specified reduction. -/
theorem wideReduceBitsLECosted_result {width : ℕ} (read : Fin width → Bool × ℕ) :
    (wideReduceBitsLECosted read).1 = ((packBitsLECosted read).1 : Fp) := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [wideReduceBitsLECosted, packBitsLECosted, ih, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
    split <;> simp only [Nat.cast_one, Nat.cast_zero] <;> ring

/-- The two counted algorithms have identical structural costs, including reader adapters. -/
theorem wideReduceBitsLECosted_cost {width : ℕ} (read : Fin width → Bool × ℕ) :
    (wideReduceBitsLECosted read).2 = (packBitsLECosted read).2 := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [wideReduceBitsLECosted, packBitsLECosted, ih]

/-- The reduction cost is bounded for every complete costed input reader. -/
theorem wideReduceBitsLECosted_cost_le {width : ℕ} (read : Fin width → Bool × ℕ)
    (access : ℕ) (haccess : ∀ bit, (read bit).2 ≤ access) :
    (wideReduceBitsLECosted read).2 ≤ width * (access + 4) + width * width + 1 := by
  rw [wideReduceBitsLECosted_cost]
  exact packBitsLECosted_cost_le read access haccess

/-- At width 512 the result is exactly the field tape already used by the simulator. -/
theorem wideReduceBitsLECosted_raw_word {count : ℕ}
    (bits : Fin (count * 512) → Bool) (access : Fin (count * 512) → ℕ)
    (word : Fin count) :
    (wideReduceBitsLECosted (fun bit : Fin 512 =>
      (bits (finProdFinEquiv (word, bit)), access (finProdFinEquiv (word, bit))))).1 =
      reduceFieldTape (rawBitsTapeEquiv count bits) word := by
  rw [wideReduceBitsLECosted_result, packBitsLECosted_raw_word]
  rfl

/-- A complete wide field reduction has the same fixed per-word cost bound. -/
theorem wideReduceBitsLECosted_raw_word_cost_le {count : ℕ}
    (bits : Fin (count * 512) → Bool) (access : Fin (count * 512) → ℕ)
    (bound : ℕ) (haccess : ∀ bit, access bit ≤ bound) (word : Fin count) :
    (wideReduceBitsLECosted (fun bit : Fin 512 =>
      (bits (finProdFinEquiv (word, bit)), access (finProdFinEquiv (word, bit))))).2 ≤
      512 * bound + 264193 := by
  rw [wideReduceBitsLECosted_cost]
  exact packBitsLECosted_raw_word_cost_le bits access bound haccess word

end Zcash.Snark.ZeroKnowledge
