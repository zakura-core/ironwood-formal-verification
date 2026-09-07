import Zcash.Snark.ZeroKnowledge.PlonkEvaluationCompression

/-!
# The verifier's complete table of compressed opening groups

The actual assembly consumes a zipped table of group commitments and scalar
vectors. The table has exactly five entries, and both projections agree with
the reference reconstruction in the same order.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp Msm Msm.zero URS)

/-- The exact compressed table constructed inside the existing verifier's `assembleOpening`. -/
def plonkVerifierCompressedGroups {actions k : ℕ} {G : Type*} [Inhabited G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    List (Msm k Fp G × List Fp) :=
  let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment
    (plonkProofFromJointView pub ch.x ch.x1 view) ch)
  (grouped.sets.zip grouped.points).map fun group => compressSet ch.x1 group.1 group.2.length

/-- The actual verifier has exactly five member groups and five matching node lists. -/
theorem plonkVerifierGroup_lengths {actions k : ℕ} {G : Type*} [Inhabited G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)
    grouped.sets.length = 5 ∧ grouped.points.length = 5 := by
  have hp : (constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)).points.length = 5 := by
    simpa only [List.length_ofFn] using congrArg List.length
      (plonkVerifierGroup_nodes vk hlayout pub instanceCommitment ch view hpositive hpoints)
  exact ⟨(constructIntermediateSets_points_length _).trans hp, hp⟩

/-- Zipping the member groups and node lists retains all five groups. -/
theorem plonkVerifierCompressedGroups_length {actions k : ℕ} {G : Type*}
    [Inhabited G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    (plonkVerifierCompressedGroups vk pub instanceCommitment ch view).length = 5 := by
  have h := plonkVerifierGroup_lengths vk hlayout pub instanceCommitment ch view hpositive hpoints
  simp only [plonkVerifierCompressedGroups, List.length_map, List.length_zip, h.1, h.2, min_self]

/-- Each in-range table entry is the compression of the corresponding derived member and node lists. -/
theorem plonkVerifierCompressedGroups_getD {actions k : ℕ} {G : Type*}
    [Inhabited G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) (i : Fin 5) :
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)
    (plonkVerifierCompressedGroups vk pub instanceCommitment ch view).getD i.val (Msm.zero k Fp G, []) =
      compressSet ch.x1 (grouped.sets.getD i.val []) (grouped.points.getD i.val []).length := by
  let grouped : MultiopenGrouped k Fp G := constructIntermediateSets (assembleQueries vk instanceCommitment
    (plonkProofFromJointView pub ch.x ch.x1 view) ch)
  have h := plonkVerifierGroup_lengths vk hlayout pub instanceCommitment ch view hpositive hpoints
  change grouped.sets.length = 5 ∧ grouped.points.length = 5 at h
  have hs : i.val < grouped.sets.length := by rw [h.1]; exact i.isLt
  have hp : i.val < grouped.points.length := by rw [h.2]; exact i.isLt
  change ((grouped.sets.zip grouped.points).map (fun group => compressSet ch.x1 group.1 group.2.length)).getD
    i.val (Msm.zero k Fp G, []) =
      compressSet ch.x1 (grouped.sets.getD i.val []) (grouped.points.getD i.val []).length
  rw [List.getD_eq_getElem _ _ (by
    simp only [List.length_map, List.length_zip, h.1, h.2, min_self]
    exact i.isLt), List.getElem_map, List.getElem_zip,
    List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ hp]

-- Index bounds should use the proved table length instead of reducing the assembler.
attribute [local irreducible] plonkVerifierCompressedGroups constructIntermediateSets assembleQueries compressSet

/-- Evaluating every compressed commitment recovers the complete reference commitment list. -/
theorem plonkVerifierCompressedGroups_commitments {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Inhabited G] [DecidableEq G] (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x))
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment) (hn : vk.n = 2048) :
    (plonkVerifierCompressedGroups vk pub instanceCommitment ch view).map (fun group => group.1.eval urs) =
      List.ofFn (plonkPublicGroupCommitments urs pub ch.x ch.x1 view.1.1) := by
  have hlength := plonkVerifierCompressedGroups_length vk hlayout pub instanceCommitment ch view hpositive hpoints
  apply List.ext_getElem (by simp only [List.length_map, List.length_ofFn, hlength])
  intro j hj hj'
  have hj5 : j < 5 := by simpa only [List.length_ofFn] using hj'
  have hjg : j < (plonkVerifierCompressedGroups vk pub instanceCommitment ch view).length := by
    rw [hlength]; exact hj5
  let i : Fin 5 := ⟨j, hj5⟩
  have hget := plonkVerifierCompressedGroups_getD vk hlayout pub instanceCommitment ch view hpositive hpoints i
  rw [List.getD_eq_getElem _ _ hjg] at hget
  simp only [List.getElem_map, List.getElem_ofFn]
  exact (congrArg (fun group : Msm urs.k Fp G × List Fp => group.1.eval urs) hget).trans
    (plonkVerifierGroup_commitment_from_layout urs vk hlayout pub instanceCommitment ch view
      hpositive hpoints hpublic hn i)

/-- The complete scalar-vector projection of the compressed table is the reference node-value table. -/
theorem plonkVerifierCompressedGroups_evaluations {actions k : ℕ} {G : Type*}
    [Inhabited G] [Zero G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    (plonkVerifierCompressedGroups vk pub instanceCommitment ch view).map Prod.snd =
      List.ofFn (plonkPublicNodeValues pub ch.x ch.x1
        (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1) := by
  have hlength := plonkVerifierCompressedGroups_length vk hlayout pub instanceCommitment ch view hpositive hpoints
  apply List.ext_getElem (by simp only [List.length_map, List.length_ofFn, hlength])
  intro j hj hj'
  have hj5 : j < 5 := by simpa only [List.length_ofFn] using hj'
  have hjg : j < (plonkVerifierCompressedGroups vk pub instanceCommitment ch view).length := by
    rw [hlength]; exact hj5
  let i : Fin 5 := ⟨j, hj5⟩
  have hget := plonkVerifierCompressedGroups_getD vk hlayout pub instanceCommitment ch view hpositive hpoints i
  rw [List.getD_eq_getElem _ _ hjg] at hget
  simp only [List.getElem_map, List.getElem_ofFn]
  exact (congrArg Prod.snd hget).trans
    (plonkVerifierGroup_evaluations_from_layout vk hlayout pub instanceCommitment ch view hpositive hpoints i)

end Zcash.Snark.ZeroKnowledge
