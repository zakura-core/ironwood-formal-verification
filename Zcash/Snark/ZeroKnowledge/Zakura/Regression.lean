import Zcash.Snark.ZeroKnowledge.Zakura.Attempt
import Zcash.Snark.ZeroKnowledge.IpaAttempt

/-!
# Boundary examples for the released proof-call observation

These examples distinguish errors from the zero-IPA panic and ensure that a
failed call does not return its retained proof prefix. Public initialization
rejects an identity independently of proof randomness.
-/

namespace Zcash.Snark.ZeroKnowledge.Zakura

open Zcash.Arithmetic (Fp)

/-- Successful calls return the proof bytes unchanged. -/
theorem completedCall_returnsBytes :
    observeAttempt ⟨[1, 2, 3], [], .complete⟩ = .proof [1, 2, 3] := rfl

/-- An identity advice commitment returns the transcript error and discards the local buffer. -/
theorem adviceIdentity_returnsError :
    observeAttempt ⟨[1, 2, 3], [], .failed .identityPoint⟩ = .error .transcript := by
  exact observeAttempt_earlyIdentity _ _ (by decide)

/-- Duplicate queries retain the opening-error outcome even when the challenge prefix ends in zero. -/
theorem duplicateQueries_returnError :
    observeAttempt ⟨[1, 2, 3], List.replicate 7 0, .failed .coincidentOpeningQueries⟩ =
      .error .opening := rfl

/-- An identity multi-opening quotient commitment is an opening error, before any IPA challenge. -/
theorem quotientIdentity_returnsError :
    observeAttempt ⟨[1, 2, 3], List.replicate 7 1, .failed .identityPoint⟩ = .error .opening := by
  exact observeAttempt_openingIdentity _ _ (by simp)

/-- The first zero IPA challenge causes a panic after both round points have been written. -/
theorem firstZeroIpa_panics (challenges : Challenges 11 Fp)
    (hzero : plonkAttemptChallenge challenges 11 = 0) :
    let attempt := observeProtocolTrace (fun point : UInt8 => some [point]) (fun _ => [9])
      (plonkAttemptChallenge challenges) (plonkAfterChallenge challenges) 11
      [.point 7, .point 8, .challenge, .scalar 1]
    attempt = ⟨[7, 8], [0], .failed .zeroIpaChallenge⟩ ∧ observeAttempt attempt = .panic := by
  simp [observeProtocolTrace, plonkAfterChallenge, hzero, observeAttempt]

/-- Duplicate-query rejection receives both batching challenges and emits no quotient commitment. -/
theorem duplicateQueries_stopBeforeQuotient (challenges : Challenges 11 Fp)
    (hzero : challenges.x = 0) :
    observeProtocolTrace (fun point : UInt8 => some [point]) (fun _ => [9])
      (plonkAttemptChallenge challenges) (plonkAfterChallenge challenges) 5
      [.challenge, .challenge, .point 7] =
      ⟨[], [challenges.x1, challenges.x2], .failed .coincidentOpeningQueries⟩ := by
  simp [observeProtocolTrace, plonkAfterChallenge, plonkAttemptChallenge,
    plonkChallengeSequence, hzero]

/-- Failure of the right IPA point stops before reading the zero challenge or any later round. -/
theorem rightIdentity_precedesZeroChallenge :
    observeIpaRounds (fun point : Bool => if point then some [7] else none)
      (fun _ => [9]) 1 1 [(0, true, false), (1, true, true)] =
      ⟨[7], [], .identityPoint⟩ := by
  simp [observeIpaRounds]

/-- Public identity commitments fail initialization before a proof attempt is started. -/
theorem publicIdentity_rejected :
    acceptsPublicPrefix [.scalar 1, .point 0] = false := by
  simp [acceptsPublicPrefix]

end Zcash.Snark.ZeroKnowledge.Zakura
