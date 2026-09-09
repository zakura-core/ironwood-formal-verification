import Zcash.Snark.ZeroKnowledge.StoredDigestPrefixCost
import Zcash.Snark.ZeroKnowledge.StoredPlonkProverTapes

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- Reading prepared real-prover words recovers precisely the original raw challenge prefix. -/
theorem storedPlonkProverTapesCosted_digest_result (actions read : ℕ)
    (bits : Fin ((22 + fieldSampleCount actions) * 512) → Bool) (index : ℕ) :
    let parts := splitTapeEquiv 22 (fieldSampleCount actions) (Fin challengeDigestCard)
      (rawBitsTapeEquiv (22 + fieldSampleCount actions) bits)
    (storedDigestPrefixCosted 22 read
      (storedPlonkProverTapesCosted actions read (List.ofFn bits)).1.raw index).1 =
      extendDigestTape parts.1 index := by
  rw [storedPlonkProverTapesCosted_raw_result]
  exact storedDigestPrefixCosted_result 22 (fieldSampleCount actions) read _ index

/-- Raw replies and the prepared field challenges agree even outside the declared schedule. -/
theorem storedPlonkProverTapesCosted_digest_agreement (actions read : ℕ)
    (bits : Fin ((22 + fieldSampleCount actions) * 512) → Bool) (index : ℕ) :
    let prepared := (storedPlonkProverTapesCosted actions read (List.ofFn bits)).1
    (((storedDigestPrefixCosted 22 read prepared.raw index).1).val : Fp) =
      plonkAttemptChallenge (Challenges.eraseCosts prepared.challenges) index := by
  dsimp only
  rw [storedPlonkProverTapesCosted_digest_result, storedPlonkProverTapesCosted_challenges_result]
  let parts := splitTapeEquiv 22 (fieldSampleCount actions) (Fin challengeDigestCard)
    (rawBitsTapeEquiv (22 + fieldSampleCount actions) bits)
  have h := (plonkChallengesFromDigests_extend_read (k := 11) parts.1 index).symm
  rw [plonkChallengesFromDigests_extend] at h
  exact h

/-- Every raw reply read has a fixed price derived from the complete stored word count. -/
theorem storedPlonkProverTapesCosted_digest_cost_le (actions read : ℕ)
    (bits : List Bool) (index : ℕ) :
    (storedDigestPrefixCosted 22 read
      (storedPlonkProverTapesCosted actions read bits).1.raw index).2 ≤
      2 * (22 + fieldSampleCount actions) + read + 5 := by
  have h := storedDigestPrefixCosted_cost_le 22 read
    (storedPlonkProverTapesCosted actions read bits).1.raw index
  rwa [(storedPlonkProverTapesCosted_lengths actions read bits).1] at h

end Zcash.Snark.ZeroKnowledge
