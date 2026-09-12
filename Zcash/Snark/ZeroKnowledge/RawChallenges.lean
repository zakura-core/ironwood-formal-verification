import Zcash.Snark.ZeroKnowledge.PlonkDigest

/-!
# Raw digest sequences and the existing typed challenge record

The finite digest tape is extended by zero only outside its declared budget.
Every scheduled read reduces the corresponding raw response, in the existing
PLONK and IPA order. The original post-challenge checks remain causal through
this adapter.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Totalize a finite raw digest tape without changing any scheduled entry. -/
def extendDigestTape {count : ℕ} (tape : Fin count → Fin challengeDigestCard) : ℕ → Fin challengeDigestCard :=
  fun index => if h : index < count then tape ⟨index, h⟩ else 0

/-- Every in-range read is exactly its finite-tape entry. -/
theorem extendDigestTape_fin {count : ℕ} (tape : Fin count → Fin challengeDigestCard) (i : Fin count) :
    extendDigestTape tape i.val = tape i := by
  simp only [extendDigestTape, dif_pos i.isLt]

/-- Read the raw digests into exactly the existing field-challenge record. -/
def plonkChallengesFromDigests (k : ℕ) (digests : ℕ → Fin challengeDigestCard) : Challenges k Fp :=
  plonkChallengesFromTape (fun i => ((digests i.val).val : Fp))

/-- Every scheduled receive is its raw digest reduced modulo the field order. -/
theorem plonkChallengesFromDigests_read (k : ℕ) (digests : ℕ → Fin challengeDigestCard) (index : ℕ) :
    plonkAttemptChallenge (plonkChallengesFromDigests k digests) index =
      if index < k + 11 then ((digests index).val : Fp) else 0 := by
  by_cases hi : index < k + 11
  · rw [if_pos hi]
    exact plonkAttemptChallenge_fromTape (fun i => ((digests i.val).val : Fp)) ⟨index, hi⟩
  · rw [if_neg hi]
    apply List.getD_eq_default
    rw [plonkChallengeSequence_length]
    omega

/-- Agreement of the raw-reduced prefix implies agreement of the original typed receive prefix. -/
theorem plonkChallengesFromDigests_prefix (k n : ℕ) (left right : ℕ → Fin challengeDigestCard)
    (hprefix : ∀ i < n, ((left i).val : Fp) = ((right i).val : Fp)) :
    ∀ i < n, plonkAttemptChallenge (plonkChallengesFromDigests k left) i =
      plonkAttemptChallenge (plonkChallengesFromDigests k right) i := by
  intro i hi
  rw [plonkChallengesFromDigests_read, plonkChallengesFromDigests_read, hprefix i hi]

/-- The finite raw tape is the same challenge adapter already used by digest recovery. -/
theorem plonkChallengesFromDigests_extend {k : ℕ} (tape : PlonkChallengeTape k (Fin challengeDigestCard)) :
    plonkChallengesFromDigests k (extendDigestTape tape) =
      plonkChallengesFromTape (fun i => ((tape i).val : Fp)) := by
  apply congrArg plonkChallengesFromTape
  funext i
  rw [extendDigestTape_fin]

/-- On a zero-extended tape, even the unused totalized receive reads agree. -/
theorem plonkChallengesFromDigests_extend_read {k : ℕ}
    (tape : PlonkChallengeTape k (Fin challengeDigestCard)) (index : ℕ) :
    plonkAttemptChallenge (plonkChallengesFromDigests k (extendDigestTape tape)) index =
      ((extendDigestTape tape index).val : Fp) := by
  rw [plonkChallengesFromDigests_read]
  by_cases hi : index < k + 11
  · exact if_pos hi
  · simp only [if_neg hi, extendDigestTape, dif_neg hi, Fin.val_zero, Nat.cast_zero]

/-- The existing exceptional-case checks still use only received replies after raw reduction. -/
theorem plonkAfterDigests_causal (k : ℕ) :
    ProtocolChecksCausal (fun raw i => ((raw i).val : Fp))
      (fun raw : ℕ → Fin challengeDigestCard => plonkAfterChallenge (plonkChallengesFromDigests k raw)) := by
  intro left right index hprefix
  apply plonkAfterChallenge_causal
  intro i hi
  exact plonkChallengesFromDigests_prefix k (index + 1) left right
    (fun j hj => hprefix j (by omega)) i (by omega)

end Zcash.Snark.ZeroKnowledge
