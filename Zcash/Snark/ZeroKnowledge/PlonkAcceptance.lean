import Zcash.Snark.ZeroKnowledge.PlonkVerifierOpening
import Zcash.Snark.ZeroKnowledge.PlonkChallenges
import Zcash.Snark.Soundness.Main

/-!
# Acceptance of the completed public simulation

The reference proof constructor satisfies the verifier's typed read schedule.
On good challenges, its query grouping, opening count, and inverse-denominator
checks all succeed. The public IPA completion then makes the resulting MSM
evaluate to zero. Acceptance is the existing rejecting `DeployedAccepts`
predicate, rather than the total assembler's zero fallback.

This module starts at the existing typed, post-decode verifier boundary. The
probabilistic completeness theorem separately counts failures to emit the proof.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp Msm URS omegaOf)

/-- The reference constructor supplies the last-row evaluations exactly where the verifier reads them. -/
theorem plonkProofFromJointView_wellFormed {actions k : ℕ} {G : Type*}
    (pub : PlonkPublicPolynomials actions) (x x1 : Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    proofStringWellFormed (plonkProofFromJointView pub x x1 view) = true := by
  simp only [proofStringWellFormed, permutationLastEvalsWellFormed,
    List.all_eq_true, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, id_eq]
  intro a s
  fin_cases s <;> rfl

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Inhabited G] [DecidableEq G]

omit [AddCommGroup G] [Module Fp G] in
/-- Every rejecting assembly check succeeds for a reference-shaped proof on good challenges. -/
theorem plonkProofFromJointView_assemble {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (hlayout : PlonkQueryLayout vk) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions) (hgood : PlonkChallengesGood ch)
    (hn : vk.n = 2048) (homega : vk.omega = omegaOf 11) :
    let opened := plonkVerifierOpening urs vk pub instanceCommitment ch view
    assemble? vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch =
      some (ipaFold ch.x3 opened.2 view.2.scalar view.2.blind ch.xi ch.z
        (List.ofFn ch.ipaRound) view.2.maskCommitment (List.ofFn view.2.messages) opened.1) := by
  have hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x) := by
    rw [homega]
    exact plonkQueryPoint_injective _ _ _ hgood.2.2.2.1
  have hnodes := plonkVerifierGroup_nodes vk hlayout pub instanceCommitment ch view hpositive hpoints
  have havoid : multiopenPointsAvoidX3 ch.x3
      (constructIntermediateSets (assembleQueries vk instanceCommitment
        (plonkProofFromJointView pub ch.x ch.x1 view) ch)) = true := by
    simp only [multiopenPointsAvoidX3, hnodes, homega, List.all_eq_true, List.mem_ofFn,
      forall_exists_index, forall_apply_eq_imp_iff, decide_eq_true_eq]
    intro i point hpoint heq
    exact plonkOpeningPointSets_away _ _ _ hgood.2.2.2.1 i (heq.symm ▸ hpoint)
  rw [assemble?, plonkProofFromJointView_wellFormed, if_pos rfl, hn,
    if_neg hgood.2.2.1,
    plonkVerifierGroup_duplicateGuard vk hlayout pub instanceCommitment ch view hpoints]
  dsimp only
  rw [if_pos havoid, assembleFinalMsm?]
  erw [plonkVerifierOpening_shape urs vk hlayout pub instanceCommitment ch view hpositive hpoints]
  rfl

/-- A verifying public IPA tail gives acceptance by the complete rejecting verifier. -/
theorem plonkProofFromJointView_deployedAccepts {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (hlayout : PlonkQueryLayout vk) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions) (hgood : PlonkChallengesGood ch)
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment)
    (hn : vk.n = 2048) (homega : vk.omega = omegaOf 11)
    (hipa : view.2.Verifies (plonkPublicIpaInput urs pub ch.x ch.x1 ch.x2 ch.x4
      ch.x3 ch.xi ch.z ch.ipaRound (plonkVerifierHx vk pub ch) view.1)) :
    DeployedAccepts (plonkProofShape actions urs.k) urs rfl vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch := by
  have hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x) := by
    rw [homega]
    exact plonkQueryPoint_injective _ _ _ hgood.2.2.2.1
  have hopen := plonkVerifierOpening_eq_public urs vk hlayout pub instanceCommitment ch view
    hpositive hpoints hpublic hn homega
  have hipa' : view.2.Verifies (IpaPublic.ofMsm urs
      (plonkVerifierOpening urs vk pub instanceCommitment ch view).1 ch.x3
      (plonkVerifierOpening urs vk pub instanceCommitment ch view).2 ch.xi ch.z ch.ipaRound) := by
    change view.2.Verifies (IpaPublic.ofMsm urs _ _ _ _ _ _) at hipa
    unfold IpaTranscript.Verifies IpaPublic.ofMsm ipaPublicResponse at hipa ⊢
    dsimp only at hipa ⊢
    have hcommitment := congrArg Prod.fst hopen
    have hvalue := congrArg Prod.snd hopen
    dsimp only at hcommitment hvalue
    rw [hcommitment, hvalue]
    exact hipa
  unfold DeployedAccepts
  rw [plonkProofFromJointView_assemble urs vk hlayout pub instanceCommitment ch view
    hpositive hgood hn homega]
  exact (ipaTranscript_verifier_capstone urs _ _ _ _ _ _ _).mp hipa'

end Zcash.Snark.ZeroKnowledge
