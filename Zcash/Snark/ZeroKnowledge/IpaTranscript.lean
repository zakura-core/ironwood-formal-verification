import Zcash.Snark.ZeroKnowledge.IpaProver

/-!
# The joint IPA transcript, including the final blind

The public input includes the commitment `P`, claimed evaluation `v`, generators and supplied
challenges. The honest transcript is computed from an opening `(coefficients, rho)`, sparse
mask coefficients and independent blinds. The completion function reconstructs one group
message from the final verifier equation using only public data and simulator coins.

This is a group-element transcript. Serialization failures and Fiat–Shamir programming are
not part of this module.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Public data for the IPA stage after the opening and folding challenges have been fixed. -/
structure IpaPublic (k : ℕ) (F G : Type*) where
  generators : Fin (2 ^ k) → G
  U : G
  W : G
  commitment : G
  point : F
  value : F
  xi : F
  z : F
  rounds : Fin k → F

/-- Every prover message in the IPA stage, including both final scalar responses. -/
@[ext] structure IpaTranscript (k : ℕ) (F G : Type*) where
  maskCommitment : G
  messages : Fin k → G × G
  scalar : F
  blind : F

/-- The witness vector after adding the sparse mask and subtracting the claimed evaluation. -/
def ipaMaskedVector {k : ℕ} (pub : IpaPublic k F G)
    (coefficients : Fin (2 ^ k) → F) (alphas : Fin k → F) : Fin (2 ^ k) → F :=
  coefficients + pub.xi • sparseIpaCoefficients pub.point alphas - Pi.single 0 pub.value

/-- The actual algebraic IPA prover, with each random choice supplied explicitly. -/
def honestIpaTranscript {k : ℕ} (pub : IpaPublic k F G)
    (coefficients : Fin (2 ^ k) → F) (rho : F) (alphas : Fin k → F)
    (blinds : IpaBlinds k F) : IpaTranscript k F G where
  maskCommitment := commitGen pub.generators (sparseIpaCoefficients pub.point alphas) +
    blinds.1 • pub.W
  messages := blindIpaMessages pub.W
    (ipaCoreMessages pub.z pub.U k pub.rounds (ipaMaskedVector pub coefficients alphas)
      (evalVector k pub.point) pub.generators) blinds.2
  scalar := maskedIpaScalar pub.point pub.xi pub.value pub.rounds coefficients alphas
  blind := ipaFinalBlind rho pub.xi pub.rounds blinds

/-- The public right-hand side determined by the final scalar `c`, before its blind is added. -/
def ipaPublicResponse {k : ℕ} (pub : IpaPublic k F G) (c : F) : G :=
  c • publicFold k pub.rounds pub.generators +
    (pub.z * c * publicFold k pub.rounds (evalVector k pub.point)) • pub.U

/-- The final group equation, retaining the aggregate blind as a public response. -/
def IpaTranscript.Verifies {k : ℕ} (pub : IpaPublic k F G)
    (view : IpaTranscript k F G) : Prop :=
  pub.commitment + pub.xi • view.maskCommitment - pub.value • pub.generators 0 +
      ipaMessageSum pub.rounds view.messages =
    ipaPublicResponse pub view.scalar + view.blind • pub.W

/-- Complete the transcript from freely chosen round messages and the final two scalars.

Only group operations and inversion of the public `xi` are used. No discrete logarithm,
coefficient vector, incoming commitment blind or sparse-mask coefficient is an input. -/
def completeIpaTranscript {k : ℕ} (pub : IpaPublic k F G)
    (messages : Fin k → G × G) (c f : F) : IpaTranscript k F G where
  maskCommitment := pub.xi⁻¹ •
    (ipaPublicResponse pub c + f • pub.W -
      (pub.commitment - pub.value • pub.generators 0 + ipaMessageSum pub.rounds messages))
  messages := messages
  scalar := c
  blind := f

/-- The completion function satisfies the verifier equation for nonzero `xi`. -/
theorem completeIpaTranscript_verifies {k : ℕ} (pub : IpaPublic k F G)
    (messages : Fin k → G × G) (c f : F) (hxi : pub.xi ≠ 0) :
    (completeIpaTranscript pub messages c f).Verifies pub := by
  unfold IpaTranscript.Verifies completeIpaTranscript
  simp only [smul_smul, mul_inv_cancel₀ hxi, one_smul]
  abel

/-- For fixed round messages and scalars, the verifier equation uniquely fixes the mask commitment. -/
theorem IpaTranscript.eq_complete_of_verifies {k : ℕ} (pub : IpaPublic k F G)
    (view : IpaTranscript k F G) (hxi : pub.xi ≠ 0) (h : view.Verifies pub) :
    view = completeIpaTranscript pub view.messages view.scalar view.blind := by
  have heq : (pub.commitment - pub.value • pub.generators 0 +
      ipaMessageSum pub.rounds view.messages) + pub.xi • view.maskCommitment =
      ipaPublicResponse pub view.scalar + view.blind • pub.W := by
    calc
      _ = pub.commitment + pub.xi • view.maskCommitment - pub.value • pub.generators 0 +
          ipaMessageSum pub.rounds view.messages := by abel
      _ = _ := h
  apply IpaTranscript.ext
  · change view.maskCommitment = pub.xi⁻¹ • _
    rw [← heq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hxi, one_smul]
  · rfl
  · rfl
  · rfl

private theorem innerProduct_sub {n : ℕ} (a a' b : Fin n → F) :
    innerProduct (a - a') b = innerProduct a b - innerProduct a' b := by
  simp only [innerProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem commitGen_single {n : ℕ} (g : Fin n → G) (i : Fin n) (v : F) :
    commitGen g (Pi.single i v) = v • g i := by
  unfold commitGen
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, zero_smul]
  · simp

omit [AddCommGroup G] [Module F G] in
/-- A valid claimed evaluation makes the masked vector orthogonal to the public powers vector. -/
theorem ipaMaskedVector_eval_zero {k : ℕ} (pub : IpaPublic k F G)
    (coefficients : Fin (2 ^ k) → F) (alphas : Fin k → F)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value) :
    innerProduct (ipaMaskedVector pub coefficients alphas) (evalVector k pub.point) = 0 := by
  have hs : innerProduct (sparseIpaCoefficients pub.point alphas) (evalVector k pub.point) = 0 :=
    coefficientEvaluation_sparseIpaCoefficients pub.point alphas
  change innerProduct coefficients (evalVector k pub.point) = pub.value at hv
  rw [ipaMaskedVector, innerProduct_sub, innerProduct_add, innerProduct_smul,
    hs, hv, innerProduct_single]
  simp [evalVector]

/-- The honest algebraic prover satisfies the full equation, with its actually accumulated `f`. -/
theorem honestIpaTranscript_verifies {k : ℕ} (pub : IpaPublic k F G)
    (coefficients : Fin (2 ^ k) → F) (rho : F) (alphas : Fin k → F)
    (blinds : IpaBlinds k F)
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value)
    (hu : ∀ j, pub.rounds j ≠ 0) :
    (honestIpaTranscript pub coefficients rho alphas blinds).Verifies pub := by
  have hcore := ipaCoreMessages_equation pub.z pub.U k pub.rounds
    (ipaMaskedVector pub coefficients alphas) (evalVector k pub.point) pub.generators hu
  rw [ipaMaskedVector_eval_zero pub coefficients alphas hv, mul_zero, zero_smul,
    add_zero] at hcore
  change commitGen pub.generators (ipaMaskedVector pub coefficients alphas) +
      ipaMessageSum pub.rounds (ipaCoreMessages pub.z pub.U k pub.rounds
        (ipaMaskedVector pub coefficients alphas) (evalVector k pub.point) pub.generators) =
    ipaPublicResponse pub (maskedIpaScalar pub.point pub.xi pub.value pub.rounds
      coefficients alphas) at hcore
  unfold IpaTranscript.Verifies honestIpaTranscript
  rw [ipaMessageSum_blind, ← hcore, hcommit]
  rw [ipaMaskedVector, commitGen_sub, commitGen_add_left, commitGen_smul_left,
    commitGen_single]
  unfold ipaFinalBlind
  module

end Zcash.Snark.ZeroKnowledge
