import Zcash.Snark.ZeroKnowledge.StoredRowsCost
import Zcash.Snark.ZeroKnowledge.FiniteArithmeticCost
import Zcash.Snark.ZeroKnowledge.RawFieldTape

/-!
# Wide reduction of stored bounded words

The input representation is a stored list of 512-bit words. As in the canonical
byte encoder, bounded-width natural remainder and construction of its result
each cost one structural unit. The reduction therefore pays two units in
addition to the complete word-reader cost. This primitive convention does not
give unbounded natural arithmetic a constant price: every source word has the
fixed `challengeDigestCard = 2^512` bound.

The stored-bit implementation is separately counted in `StoredBitTapeCost`.
This adapter handles the raw-word input of the existing PRNG security game.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- Reduce the supplied 512-bit representative, retaining its full access cost. -/
def rawFieldWordCosted (value : Fin challengeDigestCard × ℕ) : Fp × ℕ :=
  ((value.1.val : Fp), value.2 + 2)

/-- The primitive returns precisely the field reduction used at the raw-tape boundary. -/
theorem rawFieldWordCosted_result (value : Fin challengeDigestCard × ℕ) :
    (rawFieldWordCosted value).1 = (value.1.val : Fp) := rfl

/-- Both bounded-width conversion operations and the inherited read are charged. -/
theorem rawFieldWordCosted_cost (value : Fin challengeDigestCard × ℕ) :
    (rawFieldWordCosted value).2 = value.2 + 2 := rfl

/-- Materialize a fixed number of reductions from the original stored word list. -/
def storedRawFieldsCosted (count read : ℕ) (raw : List (Fin challengeDigestCard)) : List Fp × ℕ :=
  ofFnCosted (fun index : Fin count =>
    rawFieldWordCosted (getDListCosted read (0 : Fin challengeDigestCard) raw index.val))

/-- Every stored word is selected in source order; missing entries retain the original zero default. -/
theorem storedRawFieldsCosted_result (count read : ℕ) (raw : List (Fin challengeDigestCard)) :
    (storedRawFieldsCosted count read raw).1 =
      List.ofFn (fun index : Fin count => ((raw.getD index.val 0).val : Fp)) := by
  simp only [storedRawFieldsCosted, ofFnCosted_result, rawFieldWordCosted_result, getDListCosted_result]

/-- The reduced output has the requested finite capacity on every input list. -/
theorem storedRawFieldsCosted_length (count read : ℕ) (raw : List (Fin challengeDigestCard)) :
    (storedRawFieldsCosted count read raw).1.length = count := ofFnCosted_length _

/-- Materializing a complete raw tape gives the exact original reduced field tape. -/
theorem storedRawFieldsCosted_ofFn_result (count read : ℕ) (raw : Fin count → Fin challengeDigestCard) :
    (storedRawFieldsCosted count read (List.ofFn raw)).1 = List.ofFn (reduceFieldTape raw) := by
  rewrite [storedRawFieldsCosted_result]
  apply congrArg List.ofFn
  funext index
  have h := getDListCosted_ofFn_result read (0 : Fin challengeDigestCard) raw index
  rewrite [getDListCosted_result] at h
  exact congrArg (fun value : Fin challengeDigestCard => (value.val : Fp)) h

/-- The full bound includes every indexed input traversal, reduction, and output cell. -/
theorem storedRawFieldsCosted_cost_le (count read : ℕ) (raw : List (Fin challengeDigestCard)) :
    (storedRawFieldsCosted count read raw).2 ≤
      count * (2 * raw.length + read + 4) + count * count + 1 := by
  apply ofFnCosted_cost_le _ (2 * raw.length + read + 3)
  intro index
  have h := getDListCosted_cost_le read (0 : Fin challengeDigestCard) raw index.val
  dsimp only [rawFieldWordCosted]
  omega

end Zcash.Snark.ZeroKnowledge
