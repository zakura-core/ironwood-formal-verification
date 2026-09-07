import Zcash.Snark.ZeroKnowledge.PlonkProofString
import Zcash.Snark.ZeroKnowledge.PlonkPublicOpening
import Zcash.Snark.Verifier.QueryCommitment
import Zcash.Snark.Soundness.Composition.Quotient
import Zcash.Snark.Soundness.Multiopen.Deployed

/-!
# Commitment slots on the actual verifier grouping path

The verifier resolves private commitments from the reference proof's emitted slots,
and reassembles the quotient commitment with the same weights as the prover. Public
instance, fixed, and sigma commitments have an explicit agreement condition.

The commitment IDs below follow the prover's Horner order. The verifier processes
each group in reverse order with ascending powers. Establishing its exact ID lists
from the query layout is a separate combinatorial obligation.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)

/-- The existing verifier slot that names each private prover column. -/
def plonkPrivateCommitmentId {actions : ℕ} : PrivateColumnId actions → CommitmentId
  | .advice a c => .adviceCol a.val c.val
  | .lookupInput a l => .lookupPermInput a.val l.val
  | .lookupTable a l => .lookupPermTable a.val l.val
  | .permutationProduct a s => .permProduct a.val s.val
  | .lookupProduct a l => .lookupProduct a.val l.val

/-- The five commitment-ID lists in the prover's polynomial Horner order. -/
def plonkOpeningCommitmentIds (actions : ℕ) : Fin 5 → List CommitmentId :=
  Fin.cons
    ((List.finRange actions).flatMap (fun a =>
      [.instanceCol a.val 0] ++ (List.finRange 3).map (fun l => .lookupPermTable a.val l.val)) ++
      (List.finRange 29).map (fun j => .fixedCol (plonkFixedQueryOrder j).val) ++
      (List.finRange 15).map (fun j => .permCommon j.val) ++ [.vanishingH, .randomPoly])
    (fun i => (plonkPrivateGroupMembers actions i).map plonkPrivateCommitmentId)

section Commitments

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Inhabited G]

/-- Agreement of the verifier's public commitment sources with the reference public polynomials. -/
structure PlonkPublicCommitmentsMatch {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) : Prop where
  instances : ∀ a, instanceCommitment a 0 = polynomialCommitment urs.g urs.w (pub.instances a) 1
  fixed : ∀ c : Fin 29, vk.fixedCommitment c.val = polynomialCommitment urs.g urs.w (pub.fixed c) 1
  sigma : ∀ c : Fin 15,
    vk.permutationCommonCommitment c = polynomialCommitment urs.g urs.w (pub.sigma c) 1

omit [AddCommGroup G] [Module Fp G] in
/-- Every private column is resolved to the exact point emitted in its reference-proof slot. -/
theorem plonkProofFromJointView_privateCommitment {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (id : PrivateColumnId actions) :
    assembledCommitment vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view)
        ch (plonkPrivateCommitmentId id) = .point (plonkColumnEntry view.1.1 id) := by
  cases id <;>
    simp [plonkPrivateCommitmentId, assembledCommitment, plonkProofFromJointView,
      plonkProofString, finFnG, plonkProofShape, FixtureMax.shape]

/-- The verifier's quotient MSM is the same weighted point used by the reference opening. -/
theorem plonkProofFromJointView_quotientCommitment {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hn : vk.n = 2048) :
    (assembledCommitment vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view)
        ch .vanishingH).eval urs = plonkCollapsedQuotientPoint ch.x view.1.1 := by
  simp only [assembledCommitment, CommitmentRef.eval, hn, plonkProofFromJointView, plonkProofString]
  change (vanishingHCommitment urs.k (ch.x ^ 2048) (List.ofFn (plonkPieceEntry view.1.1))).eval urs = _
  rw [vanishingHCommitment_eval urs]
  simp only [List.length_ofFn]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val < (List.ofFn (plonkPieceEntry view.1.1)).length := by
    simpa only [List.length_ofFn] using j.isLt
  simp only [List.getD_eq_getElem _ _ hj, List.getElem_ofFn, pow_mul]

/-- Resolving the declared group IDs recovers the reference prover's public commitment members. -/
theorem plonkOpeningCommitmentIds_commitments {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment) (hn : vk.n = 2048)
    (i : Fin 5) :
    (plonkOpeningCommitmentIds actions i).map (fun id =>
        (assembledCommitment vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch id).eval urs) =
      plonkPublicCommitmentMembers urs pub ch.x view.1.1 i := by
  have hprivate (id : PrivateColumnId actions) :=
    congrArg (CommitmentRef.eval urs)
      (plonkProofFromJointView_privateCommitment urs vk pub instanceCommitment ch view id)
  have hquotient := plonkProofFromJointView_quotientCommitment urs vk pub instanceCommitment ch view hn
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [plonkOpeningCommitmentIds, Fin.cons_zero, List.map_append, List.map_flatMap,
      List.map_map, List.map_cons, List.map_nil, Function.comp_def, plonkPublicCommitmentMembers]
    simp only [hquotient]
    simp [assembledCommitment, hpublic.instances, hpublic.fixed, hpublic.sigma,
      plonkProofFromJointView, plonkProofString, finFnG,
      CommitmentRef.eval, plonkProofShape, FixtureMax.shape]
  · simp only [plonkOpeningCommitmentIds, Fin.cons_succ, List.map_map, Function.comp_def,
      plonkPublicCommitmentMembers]
    apply List.map_congr_left
    intro id _
    exact hprivate id

omit [Inhabited G] in
/-- The verifier's ascending powers are the prover's Horner fold of the reversed member list. -/
theorem plonkCompressSet_commitment (urs : URS G) (x1 : Fp)
    (members : List (CommitmentRef urs.k Fp G × List Fp)) (numPoints : ℕ) :
    (compressSet x1 members numPoints).1.eval urs =
      commitmentHornerFold x1 (members.reverse.map fun member => member.1.eval urs) := by
  rw [compressSet_fst_eval, commitmentHornerFold, List.foldl_map,
    foldl_smul_add_powerForm x1 (fun member => member.1.eval urs) (.point 0, []) members.reverse 0]
  simp

/-- Every member routed by the actual verifier carries the commitment named by its routed ID. -/
theorem plonkVerifierGroup_commitmentMembers {actions : ℕ} [DecidableEq G] (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (instanceCommitment : Fin actions → ℕ → G)
    (ps : ProofString (plonkProofShape actions urs.k) Fp G) (ch : Challenges urs.k Fp)
    (i : ℕ) :
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)
    (grouped.sets.getD i []).map (fun member => member.1.eval urs) =
      (grouped.ids.getD i []).map (fun id => (assembledCommitment vk instanceCommitment ps ch id).eval urs) := by
  let queries := assembleQueries vk instanceCommitment ps ch
  change ((constructIntermediateSets queries).sets.getD i []).map _ =
    ((constructIntermediateSets queries).ids.getD i []).map _
  apply List.ext_getElem
  · simpa only [List.length_map] using (constructIntermediateSets_sets_ids_aligned queries i).symm
  · intro j hj hji
    simp only [List.length_map] at hj hji
    simp only [List.getElem_map]
    have hroute := constructIntermediateSets_member_commitment_eq_of_id queries
      (assembledCommitment vk instanceCommitment ps ch)
      (fun q hq => assembleQueries_commitment_eq_assembled vk instanceCommitment ps ch hq)
      i j hj .vanishingH rfl (.point 0, [])
    simpa only [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hji] using
      congrArg (CommitmentRef.eval urs) hroute

/-- Once the routed ID order is established, the verifier computes the exact reference group commitment. -/
theorem plonkVerifierGroup_commitment {actions : ℕ} [DecidableEq G] (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (instanceCommitment : Fin actions → ℕ → G) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpublic : PlonkPublicCommitmentsMatch urs vk pub instanceCommitment) (hn : vk.n = 2048)
    (i : Fin 5)
    (hids : (constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)).ids.getD i.val [] =
        (plonkOpeningCommitmentIds actions i).reverse) :
    let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)
    (compressSet ch.x1 (grouped.sets.getD i.val []) (grouped.points.getD i.val []).length).1.eval urs =
      plonkPublicGroupCommitments urs pub ch.x ch.x1 view.1.1 i := by
  let grouped : MultiopenGrouped urs.k Fp G := constructIntermediateSets
    (assembleQueries vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch)
  change (compressSet ch.x1 (grouped.sets.getD i.val [])
    (grouped.points.getD i.val []).length).1.eval urs = _
  refine (plonkCompressSet_commitment urs ch.x1 (grouped.sets.getD i.val [])
    (grouped.points.getD i.val []).length).trans ?_
  change grouped.ids.getD i.val [] = _ at hids
  have hmembers := plonkVerifierGroup_commitmentMembers urs vk instanceCommitment
    (plonkProofFromJointView pub ch.x ch.x1 view) ch i.val
  change (grouped.sets.getD i.val []).map _ = (grouped.ids.getD i.val []).map _ at hmembers
  rw [List.map_reverse]
  refine (congrArg (fun members : List G => commitmentHornerFold ch.x1 members.reverse) hmembers).trans ?_
  rw [hids, List.map_reverse, List.reverse_reverse,
    plonkOpeningCommitmentIds_commitments urs vk pub instanceCommitment ch view hpublic hn]
  rfl

end Commitments

end Zcash.Snark.ZeroKnowledge
