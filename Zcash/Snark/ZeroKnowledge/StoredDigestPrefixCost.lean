import Zcash.Snark.ZeroKnowledge.PlonkStoredTapeBound
import Zcash.Snark.ZeroKnowledge.RawChallenges

/-!
# Counted reads of the public reply prefix

The stored word list also contains the simulator's private suffix. The reply
reader explicitly returns zero after the public prefix, so those private words
cannot become raw oracle replies, even at an out-of-schedule index.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- Read only the declared public prefix; every later index returns zero. -/
def storedDigestPrefixCosted (count read : ℕ) (raw : List (Fin challengeDigestCard)) (index : ℕ) :
    Fin challengeDigestCard × ℕ :=
  if index < count then
    let value := getDListCosted read (0 : Fin challengeDigestCard) raw index
    (value.1, value.2 + 3)
  else (0, 3)

/-- The stored prefix reader is exactly the original zero-extended finite raw tape. -/
theorem storedDigestPrefixCosted_result (count suffix read : ℕ)
    (raw : Fin (count + suffix) → Fin challengeDigestCard) (index : ℕ) :
    (storedDigestPrefixCosted count read (List.ofFn raw) index).1 =
      extendDigestTape ((splitTapeEquiv count suffix (Fin challengeDigestCard) raw).1) index := by
  by_cases hi : index < count
  · simp only [storedDigestPrefixCosted, if_pos hi, extendDigestTape, dif_pos hi]
    exact getDListCosted_ofFn_result read (0 : Fin challengeDigestCard) raw
      (Fin.castAdd suffix ⟨index, hi⟩)
  · simp only [storedDigestPrefixCosted, if_neg hi, extendDigestTape, dif_neg hi]

/-- Prefix selection retains the full stored-list traversal cost. -/
theorem storedDigestPrefixCosted_cost_le (count read : ℕ)
    (raw : List (Fin challengeDigestCard)) (index : ℕ) :
    (storedDigestPrefixCosted count read raw index).2 ≤ 2 * raw.length + read + 5 := by
  have h := getDListCosted_cost_le read (0 : Fin challengeDigestCard) raw index
  by_cases hi : index < count
  · simp only [storedDigestPrefixCosted, if_pos hi]
    omega
  · simp only [storedDigestPrefixCosted, if_neg hi]
    omega

/-- Reading prepared simulator words recovers precisely the original raw challenge prefix. -/
theorem storedPlonkSimulatorTapesCosted_digest_result (actions k read : ℕ)
    (bits : Fin (((k + 11) + plonkSimulatorSampleCount actions k) * 512) → Bool) (index : ℕ) :
    let parts := splitTapeEquiv (k + 11) (plonkSimulatorSampleCount actions k) (Fin challengeDigestCard)
      (rawBitsTapeEquiv ((k + 11) + plonkSimulatorSampleCount actions k) bits)
    (storedDigestPrefixCosted (k + 11) read
      (storedPlonkSimulatorTapesCosted actions k read (List.ofFn bits)).1.raw index).1 =
      extendDigestTape parts.1 index := by
  rw [storedPlonkSimulatorTapesCosted_raw_result]
  exact storedDigestPrefixCosted_result (k + 11) (plonkSimulatorSampleCount actions k) read _ index

/-- Raw replies and the prepared field challenges agree even outside the declared schedule. -/
theorem storedPlonkSimulatorTapesCosted_digest_agreement (actions k read : ℕ)
    (bits : Fin (((k + 11) + plonkSimulatorSampleCount actions k) * 512) → Bool) (index : ℕ) :
    let prepared := (storedPlonkSimulatorTapesCosted actions k read (List.ofFn bits)).1
    (((storedDigestPrefixCosted (k + 11) read prepared.raw index).1).val : Fp) =
      plonkAttemptChallenge (Challenges.eraseCosts prepared.challenges) index := by
  dsimp only
  rw [storedPlonkSimulatorTapesCosted_digest_result, storedPlonkSimulatorTapesCosted_challenges_result]
  let parts := splitTapeEquiv (k + 11) (plonkSimulatorSampleCount actions k) (Fin challengeDigestCard)
    (rawBitsTapeEquiv ((k + 11) + plonkSimulatorSampleCount actions k) bits)
  have h := (plonkChallengesFromDigests_extend_read (k := k) parts.1 index).symm
  rw [plonkChallengesFromDigests_extend] at h
  exact h

/-- Every raw reply read has a fixed price derived from the complete stored word count. -/
theorem storedPlonkSimulatorTapesCosted_digest_cost_le (actions k read : ℕ)
    (bits : List Bool) (index : ℕ) :
    (storedDigestPrefixCosted (k + 11) read
      (storedPlonkSimulatorTapesCosted actions k read bits).1.raw index).2 ≤
      2 * ((k + 11) + plonkSimulatorSampleCount actions k) + read + 5 := by
  have h := storedDigestPrefixCosted_cost_le (k + 11) read
    (storedPlonkSimulatorTapesCosted actions k read bits).1.raw index
  rwa [storedPlonkSimulatorTapesCosted_raw_length] at h

end Zcash.Snark.ZeroKnowledge
