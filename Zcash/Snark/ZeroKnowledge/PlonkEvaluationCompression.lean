import Zcash.Snark.ZeroKnowledge.PlonkEvaluationRouting
import Zcash.Snark.Soundness.Multiopen.NodeBinding

/-!
# Verifier compression of the reference scalar claims

The verifier accumulates ascending powers over its reversed member order. This
is precisely the reference Horner fold. The existing per-member evaluation
length invariant prevents the compression's zip operation from dropping nodes.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp Msm Msm.zero)

/-- Horner folding a reversed projected list gives ascending powers over the original list. -/
theorem plonkScalarFold_reverse {α : Type*} (x1 : Fp) (value : α → Fp) (default : α) (entries : List α) :
    plonkScalarFold x1 (entries.reverse.map value) =
      ∑ m ∈ Finset.range entries.length, x1 ^ m * value (entries.getD m default) := by
  rw [plonkScalarFold, List.foldl_map]
  have h := foldl_smul_add_powerForm x1 value default entries.reverse (0 : Fp)
  simpa [smul_eq_mul, mul_comm] using h

private theorem openingNodes_getD (omega x : Fp) (nodes : List (List Fp))
    (hnodes : nodes = List.ofFn (plonkOpeningPointSets omega x)) (i : Fin 5) :
    nodes.getD i.val [] = (plonkGroupPointLabels i).map (plonkQueryPoint omega x) := by
  rw [hnodes, List.getD_eq_getElem _ _ (by
    simp only [List.length_ofFn]
    exact i.isLt), List.getElem_ofFn]
  exact (plonkGroupPointLabels_nodes omega x i).symm

/-- At each declared node the verifier's compressed evaluation is the reference scalar Horner fold. -/
theorem plonkVerifierGroup_compressedClaim {actions k : ℕ} {G : Type*}
    [Inhabited G] [Zero G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x))
    (i : Fin 5) (point : Fin 4) (hpoint : point.val ∈ plonkGroupPointIndices i) :
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)
    (compressSet ch.x1 (grouped.sets.getD i.val []) (grouped.points.getD i.val []).length).2.getD
        ((grouped.points.getD i.val []).idxOf (plonkQueryPoint vk.omega ch.x point)) 0 =
      plonkScalarFold ch.x1 ((plonkOpeningCommitmentIds actions i).map (fun id =>
        plonkQueryClaim pub ch.x (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1 id point)) := by
  let queries : List (VerifierQuery k Fp G) := assembleQueries vk instanceCommitment
    (plonkProofFromJointView pub ch.x ch.x1 view) ch
  let grouped := constructIntermediateSets queries
  let ids := plonkOpeningCommitmentIds actions i
  let claim := fun id => plonkQueryClaim pub ch.x
    (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1 id point
  have hnodes := plonkVerifierGroup_nodes vk hlayout pub instanceCommitment ch view hpositive hpoints
  change grouped.points = List.ofFn (plonkOpeningPointSets vk.omega ch.x) at hnodes
  have hnodesI := openingNodes_getD vk.omega ch.x grouped.points hnodes i
  have hnode : plonkQueryPoint vk.omega ch.x point ∈ grouped.points.getD i.val [] := by
    rw [hnodesI]
    exact List.mem_map.mpr ⟨point, (plonkGroupPointLabels_mem i point).mpr hpoint, rfl⟩
  have hindex := List.idxOf_lt_length_iff.mpr hnode
  have hcompress := compressSet_snd_getD ch.x1 (grouped.sets.getD i.val []) (.point 0, [])
    hindex (constructIntermediateSets_eval_length queries i.val)
  have hids := plonkVerifierGroup_ids vk hlayout pub instanceCommitment ch view hpositive hpoints i
  change grouped.ids.getD i.val [] = ids.reverse at hids
  have hlength : (grouped.sets.getD i.val []).length = ids.reverse.length :=
    (constructIntermediateSets_sets_ids_aligned queries i.val).symm.trans (congrArg List.length hids)
  refine hcompress.trans ?_
  rw [hlength]
  calc
    _ = ∑ m ∈ Finset.range ids.reverse.length, ch.x1 ^ m * claim (ids.reverse.getD m .vanishingH) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply congrArg (fun value : Fp => ch.x1 ^ m * value)
      exact plonkVerifierGroup_memberClaim vk hlayout pub instanceCommitment ch view hpositive hpoints
        i m (Finset.mem_range.mp hm) point hpoint
    _ = plonkScalarFold ch.x1 (ids.map claim) := by
      simpa only [List.reverse_reverse] using
        (plonkScalarFold_reverse ch.x1 claim .vanishingH ids.reverse).symm

private theorem compressionLength {k : ℕ} {F G : Type*} [Field F] (x1 : F) (numPoints : ℕ)
    (members : List (CommitmentRef k F G × List F)) (hlens : ∀ member ∈ members, member.2.length = numPoints) :
    ∀ state : Msm k F G × List F × F, state.2.1.length = numPoints →
      (members.foldl (fun state member =>
        (accumulateCommitment state.2.2 member.1 state.1,
          (state.2.1.zip member.2).map (fun entry => entry.1 + entry.2 * state.2.2),
          state.2.2 * x1)) state).2.1.length = numPoints := by
  induction members with
  | nil => intro state hstate; exact hstate
  | cons member members ih =>
    intro state hstate
    rw [List.foldl_cons]
    apply ih (fun entry hentry => hlens entry (List.mem_cons_of_mem _ hentry))
    simp only [List.length_map, List.length_zip, hstate, hlens member List.mem_cons_self, min_self]

/-- Equal member lengths make the compression's zip preserve every declared node. -/
theorem plonkCompressSet_evaluationLength {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (members : List (CommitmentRef k F G × List F)) (numPoints : ℕ)
    (hlens : ∀ member ∈ members, member.2.length = numPoints) :
    (compressSet x1 members numPoints).2.length = numPoints := by
  exact compressionLength x1 numPoints members hlens
    (Msm.zero k F G, List.replicate numPoints 0, 1) (by simp)

-- Keep index-bound checks structural: the proved equations expose the needed
-- lengths and nodes without reducing the full query assembly and compression.
attribute [local irreducible] constructIntermediateSets assembleQueries compressSet

/-- The complete compressed evaluation vector equals the reference reconstruction, with all routing derived. -/
theorem plonkVerifierGroup_evaluations_from_layout {actions k : ℕ} {G : Type*}
    [Inhabited G] [Zero G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x))
    (i : Fin 5) :
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)
    (compressSet ch.x1 (grouped.sets.getD i.val []) (grouped.points.getD i.val []).length).2 =
      plonkPublicNodeValues pub ch.x ch.x1
        (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1 i := by
  let queries : List (VerifierQuery k Fp G) := assembleQueries vk instanceCommitment
    (plonkProofFromJointView pub ch.x ch.x1 view) ch
  let grouped := constructIntermediateSets queries
  change (compressSet ch.x1 (grouped.sets.getD i.val []) (grouped.points.getD i.val []).length).2 = _
  rw [← plonkQueryClaims_nodeValues]
  have hnodes := plonkVerifierGroup_nodes vk hlayout pub instanceCommitment ch view hpositive hpoints
  change grouped.points = List.ofFn (plonkOpeningPointSets vk.omega ch.x) at hnodes
  have hnodesI := openingNodes_getD vk.omega ch.x grouped.points hnodes i
  have hlength := plonkCompressSet_evaluationLength ch.x1 (grouped.sets.getD i.val [])
    (grouped.points.getD i.val []).length (constructIntermediateSets_eval_length queries i.val)
  apply List.ext_getElem
  · simpa only [hnodesI, List.length_map] using hlength
  · intro j hj hj'
    simp only [List.length_map] at hj'
    let point := (plonkGroupPointLabels i)[j]
    have hpoint := (plonkGroupPointLabels_mem i point).mp (List.getElem_mem hj')
    have hindex : ((plonkGroupPointLabels i).map (plonkQueryPoint vk.omega ch.x)).idxOf
        (plonkQueryPoint vk.omega ch.x point) = j := by
      have h := ((plonkGroupPointLabels_nodup i).map hpoints).idxOf_getElem
        j (by simpa only [List.length_map] using hj')
      simpa only [List.getElem_map] using h
    have hindexActual : (grouped.points.getD i.val []).idxOf
        (plonkQueryPoint vk.omega ch.x point) = j := by
      rw [hnodesI]
      exact hindex
    have h := plonkVerifierGroup_compressedClaim vk hlayout pub instanceCommitment ch view
      hpositive hpoints i point hpoint
    change (compressSet ch.x1 (grouped.sets.getD i.val []) (grouped.points.getD i.val []).length).2.getD
      ((grouped.points.getD i.val []).idxOf (plonkQueryPoint vk.omega ch.x point)) 0 = _ at h
    rw [hindexActual, List.getD_eq_getElem _ _ hj] at h
    simpa only [List.getElem_map] using h

end Zcash.Snark.ZeroKnowledge
