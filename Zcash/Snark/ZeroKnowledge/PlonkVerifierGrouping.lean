import Zcash.Snark.ZeroKnowledge.PlonkQueryGroups

/-!
# Verifier grouping from the reference proof's query layout

The group-ID order is derived here from the actual query assembler and grouping
algorithm. Distinct rotation points and the public commitment agreement remain
explicit. The resulting commitment theorem accepts no separate routing premise.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)

section Routing

variable {G : Type*} [Inhabited G] [DecidableEq G]

/-- The verifier routes every reference commitment group in the required reverse Horner order. -/
theorem plonkVerifierGroup_ids {actions k : ℕ}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x))
    (i : Fin 5) :
    (constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)).ids.getD i.val [] =
        (plonkOpeningCommitmentIds actions i).reverse := by
  exact (congrArg (fun ids : List (List CommitmentId) => ids.getD i.val [])
    (plonkProofFromJointView_groupingIds vk hlayout pub instanceCommitment ch view hpoints)).trans
      (plonkQueryPattern_groupIds actions k hpositive i)

/-- The verifier's complete node lists agree with the reference opening-point lists. -/
theorem plonkVerifierGroup_nodes {actions k : ℕ}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    (constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)).points =
        List.ofFn (plonkOpeningPointSets vk.omega ch.x) := by
  refine (plonkProofFromJointView_groupingNodes vk hlayout pub instanceCommitment ch view hpoints).trans ?_
  rw [plonkQueryPattern_groupNodes actions k hpositive]
  simp [plonkOpeningPointSets, plonkQueryPoint, plonkQueryRotation, rotateOmega, zpow_ofNat]

end Routing

/-- The actual verifier computes the reference group commitment, with its ID order derived. -/
theorem plonkVerifierGroup_commitment_from_layout {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Inhabited G] [DecidableEq G] (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x))
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment) (hn : vk.n = 2048)
    (i : Fin 5) :
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)
    (compressSet ch.x1 (grouped.sets.getD i.val []) (grouped.points.getD i.val []).length).1.eval urs =
      plonkPublicGroupCommitments urs pub ch.x ch.x1 view.1.1 i := by
  exact plonkVerifierGroup_commitment urs vk pub instanceCommitment ch view hpublic hn i
    (plonkVerifierGroup_ids vk hlayout pub instanceCommitment ch view hpositive hpoints i)

end Zcash.Snark.ZeroKnowledge
