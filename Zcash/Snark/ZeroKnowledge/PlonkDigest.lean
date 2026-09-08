import Zcash.Snark.ZeroKnowledge.DigestTape
import Zcash.Snark.ZeroKnowledge.PlonkChallengeCausality

/-!
# Recovering raw digests in the verifier's complete challenge order

The recovery kernel reads the same `11 + k` field challenges as the attempt
observer. Its joint law is exactly an independent uniform raw digest tape
followed by the original challenge-dependent prover continuation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Read the typed verifier tape back in its specified receive order. -/
def plonkChallengeFields {k : ℕ} (ch : Challenges k Fp) : PlonkChallengeTape k Fp :=
  fun i => plonkAttemptChallenge ch i.val

/-- The receive-order reader is a left inverse of the existing tape adapter. -/
theorem plonkChallengeFields_fromTape {k : ℕ} (tape : PlonkChallengeTape k Fp) :
    plonkChallengeFields (plonkChallengesFromTape tape) = tape :=
  funext (plonkAttemptChallenge_fromTape tape)

/-- The same reader loses none of the typed verifier challenge record. -/
theorem plonkChallengesFromFields {k : ℕ} (ch : Challenges k Fp) :
    plonkChallengesFromTape (plonkChallengeFields ch) = ch := by
  apply plonkAttemptChallenge_prefix_injective
  intro i hi
  exact plonkAttemptChallenge_fromTape (plonkChallengeFields ch) ⟨i, by omega⟩

/-- Attach the raw responses corresponding to every field challenge in a joint view. -/
noncomputable def attachPlonkDigests {k : ℕ} {V : Type*} (law : PMF (Challenges k Fp × V)) :
    PMF (PlonkChallengeTape k (Fin challengeDigestCard) × (Challenges k Fp × V)) :=
  liftDigestTapeView (fun view => plonkChallengeFields view.1) law

/-- Sample all raw digests independently, then run the original field-challenge continuation. -/
noncomputable def rawDigestChallengeExperiment {V : Type*} (k : ℕ) (produce : Challenges k Fp → PMF V) :
    PMF (PlonkChallengeTape k (Fin challengeDigestCard) × (Challenges k Fp × V)) :=
  (PMF.uniformOfFintype (PlonkChallengeTape k (Fin challengeDigestCard))).bind fun digests =>
    let ch := plonkChallengesFromTape (fun i => ((digests i).val : Fp))
    (produce ch).map (fun view => (digests, (ch, view)))

/-- Recovering the full raw tape preserves the exact joint wide-challenge experiment. -/
theorem attachPlonkDigests_wideChallenges {V : Type*} (k : ℕ) (produce : Challenges k Fp → PMF V) :
    attachPlonkDigests ((widePlonkChallenges k).bind fun ch => (produce ch).map (Prod.mk ch)) =
      rawDigestChallengeExperiment k produce := by
  simp only [attachPlonkDigests, liftDigestTapeView, widePlonkChallenges,
    sampleFieldsWith_eq_independentTape, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    plonkChallengeFields_fromTape]
  calc
    _ = (independentTapeLaw fieldSample (k + 11)).bind (fun fields =>
        (digestTapeFiberSample fields).bind fun digests =>
          (produce (plonkChallengesFromTape fields)).map
            (fun view => (digests, (plonkChallengesFromTape fields, view)))) := by
      congr 1
      funext fields
      exact PMF.bind_comm _ _ _
    _ = _ := by
      rw [digestTape_recovery_law, independentTapeLaw_uniform]
      rfl

end Zcash.Snark.ZeroKnowledge
