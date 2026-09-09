import Zcash.Snark.ZeroKnowledge.WideBitReductionCost
import Zcash.Snark.ZeroKnowledge.StoredRowsCost
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost

/-!
# Full access costs for a stored Boolean tape

The input is a materialized list of bits. Each access pays for its list traversal
and for constructing the word/bit index. Both raw packing and field reduction
therefore retain the whole input-access cost. The representation theorem identifies
the existing fixed bit tape, including little-endian order and all 512 bits.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Common
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192

/-- Read one stored bit, charging the product index, addition, and reader adapter. -/
def storedWordBitCosted {count : ℕ} (read : ℕ) (bits : List Bool)
    (word : Fin count) (bit : Fin 512) : Bool × ℕ :=
  let value := getDListCosted read false bits (finProdFinEquiv (word, bit)).val
  (value.1, value.2 + 3)

/-- The stored word reader preserves the exact index in the original bit tape. -/
theorem storedWordBitCosted_encode_result {count : ℕ} (read : ℕ)
    (bits : Fin (count * 512) → Bool) (word : Fin count) (bit : Fin 512) :
    (storedWordBitCosted read (List.ofFn bits) word bit).1 = bits (finProdFinEquiv (word, bit)) :=
  getDListCosted_ofFn_result read false bits (finProdFinEquiv (word, bit))

/-- The full bit-reader bound follows from the actual stored input length. -/
theorem storedWordBitCosted_cost_le {count : ℕ} (read : ℕ) (bits : List Bool)
    (word : Fin count) (bit : Fin 512) :
    (storedWordBitCosted read bits word bit).2 ≤ 2 * bits.length + read + 4 := by
  have h := getDListCosted_cost_le read false bits (finProdFinEquiv (word, bit)).val
  dsimp only [storedWordBitCosted]
  omega

/-- Pack a complete raw word from stored bits, paying also for its bounded-word wrapper. -/
def storedRawWordCosted {count : ℕ} (read : ℕ) (bits : List Bool) (word : Fin count) :
    Fin challengeDigestCard × ℕ :=
  let packed := packBitsLECosted (storedWordBitCosted read bits word)
  (⟨packed.1, packBitsLECosted_lt _⟩, packed.2 + 1)

/-- Reduce a complete stored word directly into the protocol field. -/
def storedFieldWordCosted {count : ℕ} (read : ℕ) (bits : List Bool) (word : Fin count) : Fp × ℕ :=
  wideReduceBitsLECosted (storedWordBitCosted read bits word)

/-- Stored raw packing is exactly the existing fixed-tape packing function. -/
theorem storedRawWordCosted_encode_result {count : ℕ} (read : ℕ)
    (bits : Fin (count * 512) → Bool) (word : Fin count) :
    (storedRawWordCosted read (List.ofFn bits) word).1 = rawBitsTapeEquiv count bits word := by
  apply Fin.ext
  change (packBitsLECosted (storedWordBitCosted read (List.ofFn bits) word)).1 = _
  rw [packBitsLECosted_result, rawBitsTapeEquiv_word]
  apply Finset.sum_congr rfl
  intro bit _
  rw [storedWordBitCosted_encode_result]
  cases bits (finProdFinEquiv (word, bit)) <;> rfl

/-- Stored wide reduction gives exactly the simulator's existing reduced field tape. -/
theorem storedFieldWordCosted_encode_result {count : ℕ} (read : ℕ)
    (bits : Fin (count * 512) → Bool) (word : Fin count) :
    (storedFieldWordCosted read (List.ofFn bits) word).1 =
      reduceFieldTape (rawBitsTapeEquiv count bits) word := by
  rw [storedFieldWordCosted, wideReduceBitsLECosted_result]
  have h := congrArg Fin.val (storedRawWordCosted_encode_result read bits word)
  exact congrArg (fun value : ℕ => (value : Fp)) h

/-- Raw packing has a complete bound, including all accesses to the stored bit list. -/
theorem storedRawWordCosted_cost_le {count : ℕ} (read : ℕ) (bits : List Bool) (word : Fin count) :
    (storedRawWordCosted read bits word).2 ≤
      512 * (2 * bits.length + read + 4) + 264194 := by
  have h := packBitsLECosted_cost_le (storedWordBitCosted read bits word)
    (2 * bits.length + read + 4) (storedWordBitCosted_cost_le read bits word)
  dsimp only [storedRawWordCosted]
  omega

/-- Field reduction has a complete bound, including all accesses to the stored bit list. -/
theorem storedFieldWordCosted_cost_le {count : ℕ} (read : ℕ) (bits : List Bool) (word : Fin count) :
    (storedFieldWordCosted read bits word).2 ≤
      512 * (2 * bits.length + read + 4) + 264193 := by
  have h := wideReduceBitsLECosted_cost_le (storedWordBitCosted read bits word)
    (2 * bits.length + read + 4) (storedWordBitCosted_cost_le read bits word)
  dsimp only [storedFieldWordCosted]
  omega

/-- Fully materialize every raw word of a stored fixed bit tape. -/
def storedRawTapeCosted (count read : ℕ) (bits : List Bool) : List (Fin challengeDigestCard) × ℕ :=
  ofFnCosted (storedRawWordCosted (count := count) read bits)

/-- Fully materialize every reduced field word of a stored fixed bit tape. -/
def storedFieldTapeCosted (count read : ℕ) (bits : List Bool) : List Fp × ℕ :=
  ofFnCosted (storedFieldWordCosted (count := count) read bits)

/-- Complete raw-tape erasure preserves all original words in order. -/
theorem storedRawTapeCosted_encode_result {count : ℕ} (read : ℕ)
    (bits : Fin (count * 512) → Bool) :
    (storedRawTapeCosted count read (List.ofFn bits)).1 = List.ofFn (rawBitsTapeEquiv count bits) := by
  simp only [storedRawTapeCosted, ofFnCosted_result, storedRawWordCosted_encode_result]

/-- Complete reduced-tape erasure preserves all original field draws in order. -/
theorem storedFieldTapeCosted_encode_result {count : ℕ} (read : ℕ)
    (bits : Fin (count * 512) → Bool) :
    (storedFieldTapeCosted count read (List.ofFn bits)).1 =
      List.ofFn (reduceFieldTape (rawBitsTapeEquiv count bits)) := by
  simp only [storedFieldTapeCosted, ofFnCosted_result, storedFieldWordCosted_encode_result]

/-- The complete raw-tape cost is polynomial in word count and stored bit length. -/
theorem storedRawTapeCosted_cost_le (count read : ℕ) (bits : List Bool) :
    (storedRawTapeCosted count read bits).2 ≤
      count * (512 * (2 * bits.length + read + 4) + 264195) + count * count + 1 :=
  ofFnCosted_cost_le _ _ (storedRawWordCosted_cost_le read bits)

/-- The complete reduced-tape cost is polynomial in word count and stored bit length. -/
theorem storedFieldTapeCosted_cost_le (count read : ℕ) (bits : List Bool) :
    (storedFieldTapeCosted count read bits).2 ≤
      count * (512 * (2 * bits.length + read + 4) + 264194) + count * count + 1 :=
  ofFnCosted_cost_le _ _ (storedFieldWordCosted_cost_le read bits)

end Zcash.Snark.ZeroKnowledge
