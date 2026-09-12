import Zcash.Snark.ZeroKnowledge.IpaSampling
import Zcash.Snark.ZeroKnowledge.IpaChallenges

/-!
# The IPA prover does not read future verifier challenges

The sparse-mask commitment uses the already fixed opening point and its own
private coins. The round `j` pair uses only challenges from strictly earlier
rounds. These statements hold on every fixed private tape, including zero
challenges and invalid openings; they do not condition away exceptional cases.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The unblinded round pair uses earlier round challenges, never its own or later ones. -/
theorem ipaCoreMessages_prefix (z : F) (U : G) (k : ℕ) :
    ∀ (left right : Fin k → F) (a b : Fin (2 ^ k) → F) (g : Fin (2 ^ k) → G) (j : Fin k),
      (∀ i : Fin k, i.val < j.val → left i = right i) →
        ipaCoreMessages z U k left a b g j = ipaCoreMessages z U k right a b g j := by
  induction k with
  | zero => intro _ _ _ _ _ j; exact Fin.elim0 j
  | succ k ih =>
    intro left right a b g j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      rfl
    · intro h
      have hzero : left 0 = right 0 := h 0 (by simp)
      simp only [ipaCoreMessages, Fin.cons_succ, hzero]
      apply ih
      intro i hi
      exact h i.succ (by simpa using hi)

/-- The first commitment needs neither `xi`, `z`, round challenges, nor the opening witness. -/
theorem honestIpaTranscript_maskCommitment_agrees {k : ℕ} (pub pub' : IpaPublic k F G)
    (coefficients coefficients' : Fin (2 ^ k) → F) (rho rho' : F)
    (alphas : Fin k → F) (blinds : IpaBlinds k F)
    (hgen : pub.generators = pub'.generators) (hW : pub.W = pub'.W) (hpoint : pub.point = pub'.point) :
    (honestIpaTranscript pub coefficients rho alphas blinds).maskCommitment =
      (honestIpaTranscript pub' coefficients' rho' alphas blinds).maskCommitment := by
  simp only [honestIpaTranscript, hgen, hW, hpoint]

/-- Equal earlier public data and round coins determine the same blinded pair. -/
theorem honestIpaTranscript_messages_agree {k : ℕ} (pub pub' : IpaPublic k F G)
    (coefficients : Fin (2 ^ k) → F) (rho rho' : F) (alphas : Fin k → F)
    (blinds : IpaBlinds k F) (j : Fin k)
    (hgen : pub.generators = pub'.generators) (hW : pub.W = pub'.W) (hU : pub.U = pub'.U)
    (hpoint : pub.point = pub'.point) (hvalue : pub.value = pub'.value)
    (hxi : pub.xi = pub'.xi) (hz : pub.z = pub'.z)
    (hrounds : ∀ i : Fin k, i.val < j.val → pub.rounds i = pub'.rounds i) :
    (honestIpaTranscript pub coefficients rho alphas blinds).messages j =
      (honestIpaTranscript pub' coefficients rho' alphas blinds).messages j := by
  have hcore := ipaCoreMessages_prefix pub'.z pub'.U k pub.rounds pub'.rounds
    (ipaMaskedVector pub' coefficients alphas) (evalVector k pub'.point) pub'.generators j hrounds
  simpa only [honestIpaTranscript, blindIpaMessages, ipaMaskedVector,
    hgen, hW, hU, hpoint, hvalue, hxi, hz] using
    congrArg (fun pair : G × G =>
      (pair.1 + (blinds.2 j).1 • pub'.W, pair.2 + (blinds.2 j).2 • pub'.W)) hcore

/-- Adding the fixed private blinds preserves the strict round-prefix dependency. -/
theorem honestIpaTranscript_messages_prefix {k : ℕ} (pub : IpaPublic k F G)
    (rounds : Fin k → F) (coefficients : Fin (2 ^ k) → F) (rho : F)
    (alphas : Fin k → F) (blinds : IpaBlinds k F) (j : Fin k)
    (h : ∀ i : Fin k, i.val < j.val → pub.rounds i = rounds i) :
    (honestIpaTranscript pub coefficients rho alphas blinds).messages j =
      (honestIpaTranscript {pub with rounds := rounds} coefficients rho alphas blinds).messages j := by
  have hcore := ipaCoreMessages_prefix pub.z pub.U k pub.rounds rounds
    (ipaMaskedVector pub coefficients alphas) (evalVector k pub.point) pub.generators j h
  simpa only [honestIpaTranscript, blindIpaMessages, ipaMaskedVector] using
    congrArg (fun pair : G × G =>
      (pair.1 + (blinds.2 j).1 • pub.W, pair.2 + (blinds.2 j).2 • pub.W)) hcore

/-- The ordered private tape yields the same first commitment with arbitrary future challenges. -/
theorem ipaTranscriptFromTape_maskCommitment_agrees {k : ℕ} (pub pub' : IpaPublic k F G)
    (coefficients coefficients' : Fin (2 ^ k) → F) (rho rho' : F)
    (tape : Fin (ipaSampleCount k) → F)
    (hgen : pub.generators = pub'.generators) (hW : pub.W = pub'.W) (hpoint : pub.point = pub'.point) :
    (ipaTranscriptFromTape pub coefficients rho tape).maskCommitment =
      (ipaTranscriptFromTape pub' coefficients' rho' tape).maskCommitment :=
  honestIpaTranscript_maskCommitment_agrees pub pub' coefficients coefficients' rho rho'
    (ipaTapeEquiv k F tape).1 (ipaTapeEquiv k F tape).2 hgen hW hpoint

/-- Actual tape-based round messages cannot depend on the challenge received after them. -/
theorem ipaTranscriptFromTape_messages_prefix {k : ℕ} (pub : IpaPublic k F G)
    (rounds : Fin k → F) (coefficients : Fin (2 ^ k) → F) (rho : F)
    (tape : Fin (ipaSampleCount k) → F) (j : Fin k)
    (h : ∀ i : Fin k, i.val < j.val → pub.rounds i = rounds i) :
    (ipaTranscriptFromTape pub coefficients rho tape).messages j =
      (ipaTranscriptFromTape {pub with rounds := rounds} coefficients rho tape).messages j :=
  honestIpaTranscript_messages_prefix pub rounds coefficients rho
    (ipaTapeEquiv k F tape).1 (ipaTapeEquiv k F tape).2 j h

/-- The full IPA challenge-tape adapter preserves the same strict dependency. -/
theorem ipaTranscriptFromTape_withChallenges_messages_agree {k : ℕ} (pub : IpaPublic k F G)
    (left right : IpaChallengeTape k F) (coefficients : Fin (2 ^ k) → F) (rho : F)
    (tape : Fin (ipaSampleCount k) → F) (j : Fin k)
    (hxi : left 0 = right 0) (hz : left 1 = right 1)
    (hrounds : ∀ i : Fin k, i.val < j.val → left i.succ.succ = right i.succ.succ) :
    (ipaTranscriptFromTape (pub.withChallenges left) coefficients rho tape).messages j =
      (ipaTranscriptFromTape (pub.withChallenges right) coefficients rho tape).messages j :=
  honestIpaTranscript_messages_agree (pub.withChallenges left) (pub.withChallenges right)
    coefficients rho rho (ipaTapeEquiv k F tape).1 (ipaTapeEquiv k F tape).2 j
    rfl rfl rfl rfl rfl hxi hz hrounds

end Zcash.Snark.ZeroKnowledge
