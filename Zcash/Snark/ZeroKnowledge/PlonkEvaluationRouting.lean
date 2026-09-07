import Zcash.Snark.ZeroKnowledge.PlonkQueryUniqueness
import Zcash.Snark.ZeroKnowledge.PlonkQueryClaims

/-!
# Reference scalar claims in the verifier's routed members

The slot order, point-set classification, flat scalar stream, and duplicate guard
together identify every member evaluation read by the existing verifier. Neither
query membership nor a routed-ID agreement is supplied as a separate premise.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Every routed member reads the reference slot's claimed scalar at each of its declared nodes. -/
theorem plonkVerifierGroup_memberClaim {actions k : ℕ} {G : Type*}
    [Inhabited G] [Zero G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpositive : 0 < actions) (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x))
    (i : Fin 5) (m : ℕ) (hm : m < (plonkOpeningCommitmentIds actions i).reverse.length)
    (point : Fin 4) (hpoint : point.val ∈ plonkGroupPointIndices i) :
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)
    ((grouped.sets.getD i.val []).getD m (.point 0, [])).2.getD
        ((grouped.points.getD i.val []).idxOf (plonkQueryPoint vk.omega ch.x point)) 0 =
      plonkQueryClaim pub ch.x (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1
        ((plonkOpeningCommitmentIds actions i).reverse.getD m .vanishingH) point := by
  let queries : List (VerifierQuery k Fp G) := assembleQueries vk instanceCommitment
    (plonkProofFromJointView pub ch.x ch.x1 view) ch
  let id := (plonkOpeningCommitmentIds actions i).reverse.getD m .vanishingH
  have hidMember : id ∈ plonkOpeningCommitmentIds actions i := by
    apply List.mem_reverse.mp
    dsimp only [id]
    rw [List.getD_eq_getElem _ _ hm]
    exact List.getElem_mem hm
  have hidFilter : id ∈ (plonkCommitmentOrder actions).filter
      (fun id => decide (plonkCommitmentGroup id = i)) := by
    rw [plonkCommitmentOrder_filter]
    exact hidMember
  obtain ⟨hidOrder, hgroup⟩ := List.mem_filter.mp hidFilter
  simp only [decide_eq_true_eq] at hgroup
  have hentry : (id, point) ∈ plonkQuerySpine actions := by
    apply (plonkQuerySpine_mem actions id point).mpr
    refine ⟨hidOrder, ?_⟩
    change point.val ∈ plonkGroupPointIndices (plonkCommitmentGroup id)
    rw [hgroup]
    exact hpoint
  obtain ⟨query, hquery, hidQuery, hqueryPoint, hqueryEval⟩ :=
    plonkProofFromJointView_queryClaim_exists vk hlayout pub instanceCommitment ch view (id, point) hentry
  have hids := plonkVerifierGroup_ids vk hlayout pub instanceCommitment ch view hpositive hpoints i
  change (constructIntermediateSets queries).ids.getD i.val [] = _ at hids
  have hmIds : m < ((constructIntermediateSets queries).ids.getD i.val []).length := by
    rw [hids]
    exact hm
  have hidAt : ((constructIntermediateSets queries).ids.getD i.val []).getD m .vanishingH =
      query.commId := by
    rw [hids]
    exact hidQuery.symm
  have hdup := plonkVerifierGroup_noDuplicates vk hlayout pub instanceCommitment ch view hpoints
  have heval := constructIntermediateSets_query_eval queries hquery hdup hmIds hidAt
  rw [hqueryPoint, hqueryEval] at heval
  exact heval

end Zcash.Snark.ZeroKnowledge
