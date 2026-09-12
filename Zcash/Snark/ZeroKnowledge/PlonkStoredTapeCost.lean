import Zcash.Snark.ZeroKnowledge.StoredBitTapeCost
import Zcash.Snark.ZeroKnowledge.PlonkChallengeReadCost
import Zcash.Snark.ZeroKnowledge.PlonkCoinReadBound

/-!
# Complete simulator tape production from stored bits

Raw oracle replies and all reduced fields are materialized from the same input
bits. Packing twice is conservative work, and preserves the original correlation
between the raw replies and their field challenges. The prefix and private suffix
are the existing exact tape split, with all eager preparation costs included.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- Stored raw replies and the original challenge and private-coin readers. -/
structure PlonkPreparedSimulatorTapes (actions k : ℕ) where
  raw : List (Fin challengeDigestCard)
  challenges : Challenges k (Fp × ℕ)
  coins : PlonkSimulatorCoinsCosted actions k

/-- Produce the complete tapes, retaining both packing passes and every eager reader preparation. -/
def storedPlonkSimulatorTapesCosted (actions k read : ℕ) (bits : List Bool) :
    PlonkPreparedSimulatorTapes actions k × ℕ :=
  let count := (k + 11) + plonkSimulatorSampleCount actions k
  let raw := storedRawTapeCosted count read bits
  let fields := storedFieldTapeCosted count read bits
  let challenges := storedPlonkChallengesCosted k read fields.1 0
  let coins := storedPlonkCoinsCosted actions k read fields.1 (k + 11)
  ({ raw := raw.1, challenges := challenges.1, coins := coins.1 },
    raw.2 + fields.2 + challenges.2 + coins.2 + 5)

/-- The complete stored raw tape contains exactly the original number of words. -/
theorem storedPlonkSimulatorTapesCosted_raw_length (actions k read : ℕ) (bits : List Bool) :
    (storedPlonkSimulatorTapesCosted actions k read bits).1.raw.length =
      (k + 11) + plonkSimulatorSampleCount actions k :=
  ofFnCosted_length _

/-- The raw output preserves every packed word of the original fixed bit tape. -/
theorem storedPlonkSimulatorTapesCosted_raw_result (actions k read : ℕ)
    (bits : Fin (((k + 11) + plonkSimulatorSampleCount actions k) * 512) → Bool) :
    (storedPlonkSimulatorTapesCosted actions k read (List.ofFn bits)).1.raw =
      List.ofFn (rawBitsTapeEquiv ((k + 11) + plonkSimulatorSampleCount actions k) bits) :=
  storedRawTapeCosted_encode_result read bits

/-- Challenge routing preserves the exact raw-response prefix, reduced in the protocol field. -/
theorem storedPlonkSimulatorTapesCosted_challenges_result (actions k read : ℕ)
    (bits : Fin (((k + 11) + plonkSimulatorSampleCount actions k) * 512) → Bool) :
    let parts := splitTapeEquiv (k + 11) (plonkSimulatorSampleCount actions k) (Fin challengeDigestCard)
      (rawBitsTapeEquiv ((k + 11) + plonkSimulatorSampleCount actions k) bits)
    Challenges.eraseCosts (storedPlonkSimulatorTapesCosted actions k read (List.ofFn bits)).1.challenges =
      plonkChallengesFromTape (reduceFieldTape parts.1) := by
  let raw := rawBitsTapeEquiv ((k + 11) + plonkSimulatorSampleCount actions k) bits
  change Challenges.eraseCosts
    (storedPlonkChallengesCosted k read
      (storedFieldTapeCosted ((k + 11) + plonkSimulatorSampleCount actions k) read (List.ofFn bits)).1 0).1 = _
  rw [storedPlonkChallengesCosted_result, storedFieldTapeCosted_encode_result]
  apply congrArg (plonkChallengesFromTape (k := k))
  funext index
  change (List.ofFn (reduceFieldTape raw)).getD (0 + index.val) 0 =
    reduceFieldTape raw (Fin.castAdd (plonkSimulatorSampleCount actions k) index)
  simpa only [getDListCosted_result, Fin.val_castAdd, Nat.zero_add] using
    getDListCosted_ofFn_result read (0 : Fp) (reduceFieldTape raw)
      (Fin.castAdd (plonkSimulatorSampleCount actions k) index)

/-- Private-coin routing preserves the exact suffix after all raw verifier replies. -/
theorem storedPlonkSimulatorTapesCosted_coins_result (actions k read : ℕ)
    (bits : Fin (((k + 11) + plonkSimulatorSampleCount actions k) * 512) → Bool) :
    let parts := splitTapeEquiv (k + 11) (plonkSimulatorSampleCount actions k) (Fin challengeDigestCard)
      (rawBitsTapeEquiv ((k + 11) + plonkSimulatorSampleCount actions k) bits)
    (storedPlonkSimulatorTapesCosted actions k read (List.ofFn bits)).1.coins.erase =
      plonkSimulatorTapeEquiv actions k (reduceFieldTape parts.2) := by
  let raw := rawBitsTapeEquiv ((k + 11) + plonkSimulatorSampleCount actions k) bits
  change (storedPlonkCoinsCosted actions k read
    (storedFieldTapeCosted ((k + 11) + plonkSimulatorSampleCount actions k) read (List.ofFn bits)).1 (k + 11)).1.erase = _
  rw [storedPlonkCoinsCosted_result, storedFieldTapeCosted_encode_result]
  apply congrArg (plonkSimulatorTapeEquiv actions k)
  funext index
  change (List.ofFn (reduceFieldTape raw)).getD ((k + 11) + index.val) 0 =
    reduceFieldTape raw (Fin.natAdd (k + 11) index)
  simpa only [getDListCosted_result, Fin.val_natAdd] using
    getDListCosted_ofFn_result read (0 : Fp) (reduceFieldTape raw) (Fin.natAdd (k + 11) index)

end Zcash.Snark.ZeroKnowledge
