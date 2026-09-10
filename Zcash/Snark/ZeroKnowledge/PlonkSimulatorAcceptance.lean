import Zcash.Snark.ZeroKnowledge.PlonkAcceptance
import Zcash.Snark.ZeroKnowledge.PlonkFresh
import Zcash.Snark.ZeroKnowledge.PlonkChallengeBounds

/-!
# The public simulator's rejection probability

Every supported simulated proof is accepted on good challenges. Thus rejection
by the complete typed verifier has probability at most the already proved
exceptional-challenge bound. No validity or acceptance premise is supplied for
the simulator's randomly chosen proof messages.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS omegaOf scalarFieldOrder)
open Zcash.Common
open scoped ENNReal

/-- Every supported simulated IPA transcript satisfies its public equation when `xi` is nonzero. -/
theorem idealIpaSimulator_verifies_of_mem_support {F G : Type*} [Field F]
    [AddCommGroup G] [Module F G] [Fintype F] [Fintype G] {k : ℕ}
    (pub : IpaPublic k F G) (view : IpaTranscript k F G) (hxi : pub.xi ≠ 0)
    (hview : view ∈ (idealIpaSimulator pub).support) : view.Verifies pub := by
  rw [idealIpaSimulator, PMF.mem_support_bind_iff] at hview
  obtain ⟨free, _, hfree⟩ := hview
  rw [PMF.mem_support_map_iff] at hfree
  obtain ⟨c, _, rfl⟩ := hfree
  exact completeIpaTranscript_verifies pub free.1 c free.2 hxi

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]
  [Inhabited G] [DecidableEq G]

/-- On good challenges, the public simulator is supported on proofs accepted by `assemble?`. -/
theorem idealPlonkVerifierSimulator_deployedAccepts {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (hlayout : PlonkQueryLayout vk) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (ch : Challenges urs.k Fp)
    (hpositive : 0 < actions) (hgood : PlonkChallengesGood ch)
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment)
    (hn : vk.n = 2048) (homega : vk.omega = omegaOf 11)
    (proof : ProofString (plonkProofShape actions urs.k) Fp G)
    (hproof : proof ∈ (idealPlonkVerifierSimulator urs vk pub ch).support) :
    DeployedAccepts (plonkProofShape actions urs.k) urs rfl vk instanceCommitment proof ch := by
  rw [idealPlonkVerifierSimulator, PMF.mem_support_map_iff] at hproof
  obtain ⟨joint, hjoint, rfl⟩ := hproof
  rw [idealPlonkJointSimulator, PMF.mem_support_bind_iff] at hjoint
  obtain ⟨mask, _, hmask⟩ := hjoint
  rw [PMF.mem_support_map_iff] at hmask
  obtain ⟨tail, htail, rfl⟩ := hmask
  exact plonkProofFromJointView_deployedAccepts urs vk hlayout pub instanceCommitment ch
    (mask, tail) hpositive hgood hpublic hn homega
    (idealIpaSimulator_verifies_of_mem_support _ tail hgood.1 htail)

/-- The simulated proof retains precisely the supplied public challenge law. -/
theorem freshPlonkVerifierSimulator_challenges {actions : ℕ}
    (urs : URS G) (law : PMF (Challenges urs.k Fp))
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions) :
    (freshPlonkVerifierSimulator urs law vk pub).map Prod.fst = law := by
  rw [freshPlonkVerifierSimulator, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hconst (ch : Challenges urs.k Fp) :
      (idealPlonkVerifierSimulator urs vk pub ch).map (fun _ => ch) = PMF.pure ch :=
    PMF.map_const _ _
  simp_rw [hconst]
  exact PMF.bind_pure law

/-- Rejection of a supported simulated proof requires exceptional challenges. -/
theorem freshPlonkVerifierSimulator_rejection_le {actions : ℕ}
    (urs : URS G) (law : PMF (Challenges urs.k Fp))
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (hlayout : PlonkQueryLayout vk) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (hpositive : 0 < actions)
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment)
    (hn : vk.n = 2048) (homega : vk.omega = omegaOf 11) :
    (freshPlonkVerifierSimulator urs law vk pub).toOuterMeasure
        {view | ¬ DeployedAccepts (plonkProofShape actions urs.k) urs rfl vk
          instanceCommitment view.2 view.1} ≤
      law.toOuterMeasure {ch | ¬ PlonkChallengesGood ch} := by
  calc
    _ ≤ (freshPlonkVerifierSimulator urs law vk pub).toOuterMeasure
        {view | ¬ PlonkChallengesGood view.1} := by
      apply PMF.toOuterMeasure_mono
      intro view ⟨hreject, hview⟩ hgood
      rw [freshPlonkVerifierSimulator, PMF.mem_support_bind_iff] at hview
      obtain ⟨ch, _, hch⟩ := hview
      rw [PMF.mem_support_map_iff] at hch
      obtain ⟨proof, hproof, rfl⟩ := hch
      exact hreject (idealPlonkVerifierSimulator_deployedAccepts urs vk hlayout pub
        instanceCommitment ch hpositive hgood hpublic hn homega proof hproof)
    _ = _ := by
      change (freshPlonkVerifierSimulator urs law vk pub).toOuterMeasure
        (Prod.fst ⁻¹' {ch | ¬ PlonkChallengesGood ch}) = _
      rw [← PMF.toOuterMeasure_map_apply, freshPlonkVerifierSimulator_challenges]

/-- The independent wide-reduced verifier tape gives an explicit simulator rejection bound. -/
theorem widePlonkVerifierSimulator_rejection_prob_le {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (hlayout : PlonkQueryLayout vk) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (hpositive : 0 < actions)
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment)
    (hn : vk.n = 2048) (homega : vk.omega = omegaOf 11) :
    (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub).toOuterMeasure
        {view | ¬ DeployedAccepts (plonkProofShape actions urs.k) urs rfl vk
          instanceCommitment view.2 view.1} ≤
      (((urs.k + 4102 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((urs.k + 11 : ℕ) : ℝ≥0∞) * challenge255Bias) :=
  (freshPlonkVerifierSimulator_rejection_le urs (widePlonkChallenges urs.k) vk hlayout pub
    instanceCommitment hpositive hpublic hn homega).trans (widePlonkChallenges_bad_le urs.k)

end Zcash.Snark.ZeroKnowledge
