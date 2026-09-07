import Zcash.Snark.ZeroKnowledge.PlonkCompressedGroups
import Zcash.Snark.ZeroKnowledge.MultiopenAssembly

/-!
# The actual verifier opening equals the reference reconstruction

The complete query assembly, grouping, and both compression projections now
feed the existing final multi-opening combination. Equality concerns the
evaluated commitment and scalar; the two MSM representations may differ.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp Msm Msm.zero URS omegaOf)

/-- Run the existing verifier's opening assembly on the complete reference proof. -/
def plonkVerifierOpening {actions : ℕ} {G : Type*} [Inhabited G] [DecidableEq G]
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G) : Msm urs.k Fp G × Fp :=
  let proof := plonkProofFromJointView pub ch.x ch.x1 view
  let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment proof ch)
  assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 proof.multiopenQPrime (List.ofFn proof.multiopenU)
    grouped (Msm.zero urs.k Fp G)

/-- The verifier's dynamic group-count check accepts the reference proof's five quotient values. -/
theorem plonkVerifierOpening_shape {actions : ℕ} {G : Type*} [Inhabited G] [DecidableEq G]
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    let proof := plonkProofFromJointView pub ch.x ch.x1 view
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment proof ch)
    assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 proof.multiopenQPrime (List.ofFn proof.multiopenU)
      grouped (Msm.zero urs.k Fp G) = some (plonkVerifierOpening urs vk pub instanceCommitment ch view) := by
  have h := plonkVerifierGroup_lengths vk hlayout pub instanceCommitment ch view hpositive hpoints
  dsimp only
  rw [assembleOpening?]
  have hshape : (List.ofFn (plonkProofFromJointView pub ch.x ch.x1 view).multiopenU).length =
      (constructIntermediateSets (assembleQueries vk instanceCommitment
        (plonkProofFromJointView pub ch.x ch.x1 view) ch)).sets.length ∧
      (constructIntermediateSets (assembleQueries vk instanceCommitment
        (plonkProofFromJointView pub ch.x ch.x1 view) ch)).points.length =
      (constructIntermediateSets (assembleQueries vk instanceCommitment
        (plonkProofFromJointView pub ch.x ch.x1 view) ch)).sets.length := by
    constructor
    · rw [List.length_ofFn, h.1]
      rfl
    · exact h.2.trans h.1.symm
  rw [if_pos hshape]
  rfl

-- Compare the assembly stages through their proved projections without
-- evaluating the complete query grouping during definitional-equality checks.
attribute [local irreducible] constructIntermediateSets assembleQueries compressSet omegaOf
  multiopenCombine multiopenEval

/-- The actual assembled opening has exactly the reference commitment point and scalar value. -/
theorem plonkVerifierOpening_eq_public {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Inhabited G] [DecidableEq G] (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x))
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment)
    (hn : vk.n = 2048) (homega : vk.omega = omegaOf 11) :
    let actual := plonkVerifierOpening urs vk pub instanceCommitment ch view
    let reference := plonkPublicOpening urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3
      (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1
    (actual.1.eval urs, actual.2) = (reference.1.eval urs, reference.2) := by
  let grouped : MultiopenGrouped urs.k Fp G := constructIntermediateSets (assembleQueries vk instanceCommitment
    (plonkProofFromJointView pub ch.x ch.x1 view) ch)
  let compressed := plonkVerifierCompressedGroups vk pub instanceCommitment ch view
  let values := (plonkPreIpaProjection pub ch.x ch.x1 view.1).groupValues
  let nodes := plonkPublicNodeValues pub ch.x ch.x1
    (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1
  let commitments := List.ofFn fun i => (Msm.zero urs.k Fp G).appendTerm 1
    (plonkPublicGroupCommitments urs pub ch.x ch.x1 view.1.1 i)
  have hnodes := plonkVerifierGroup_nodes vk hlayout pub instanceCommitment ch view hpositive hpoints
  change grouped.points = List.ofFn (plonkOpeningPointSets vk.omega ch.x) at hnodes
  rw [homega] at hnodes
  have hevals := plonkVerifierCompressedGroups_evaluations vk hlayout pub instanceCommitment ch view
    hpositive hpoints
  change compressed.map Prod.snd = List.ofFn nodes at hevals
  have hsets : ((grouped.points.zip (compressed.map Prod.snd)).zip (List.ofFn values)).map
      (fun entry => (entry.1.1, entry.1.2, entry.2)) =
        List.ofFn (fun i => (plonkOpeningPointSets (omegaOf 11) ch.x i, nodes i, values i)) := by
    rw [hnodes, hevals]
    rfl
  have hcommitments : (compressed.map Prod.fst).map (fun msm => msm.eval urs) =
      commitments.map (fun msm => msm.eval urs) := by
    have h := plonkVerifierCompressedGroups_commitments urs vk hlayout pub instanceCommitment ch view
      hpositive hpoints hpublic hn
    simpa only [compressed, commitments, List.map_map, Function.comp_def, List.map_ofFn,
      Msm.eval_appendTerm, Msm.eval_zero, one_smul, zero_add] using h
  have hprime : (plonkProofFromJointView pub ch.x ch.x1 view).multiopenQPrime =
      plonkQuotientPrimeEntry view.1.1 := rfl
  have hvalues : (plonkProofFromJointView pub ch.x ch.x1 view).multiopenU = values := rfl
  simp only [plonkVerifierOpening, assembleOpening, plonkPublicOpening, hprime, hvalues]
  change
    let lhs := multiopenCombine ch.x4 (plonkQuotientPrimeEntry view.1.1) (compressed.map Prod.fst)
      (List.ofFn values) (multiopenEval ch.x2 ch.x3
        (((grouped.points.zip (compressed.map Prod.snd)).zip (List.ofFn values)).map
          (fun entry => (entry.1.1, entry.1.2, entry.2)))) (Msm.zero urs.k Fp G)
    let rhs := multiopenCombine ch.x4 (plonkQuotientPrimeEntry view.1.1) commitments
      (List.ofFn values) (multiopenEval ch.x2 ch.x3
        (List.ofFn (fun i => (plonkOpeningPointSets (omegaOf 11) ch.x i, nodes i, values i))))
      (Msm.zero urs.k Fp G)
    (lhs.1.eval urs, lhs.2) = (rhs.1.eval urs, rhs.2)
  rw [hsets]
  exact multiopenCombine_evaluated_congr urs ch.x4 (plonkQuotientPrimeEntry view.1.1)
    (compressed.map Prod.fst) commitments hcommitments (List.ofFn values) _

end Zcash.Snark.ZeroKnowledge
