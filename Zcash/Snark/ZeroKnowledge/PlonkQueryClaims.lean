import Zcash.Snark.ZeroKnowledge.PlonkVerifierGrouping
import Zcash.Snark.ZeroKnowledge.PlonkOpeningNodes
import Zcash.Snark.ZeroKnowledge.PlonkQueryOrderLiterals

/-!
# Scalar claims in the reference proof's verifier queries

The same slot-and-rotation pattern also determines the emitted scalar claim.
The quotient slot uses the verifier's existing inferred value; private slots
read the corresponding column observation. Unused out-of-range slots are zero.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The scalar claim attached to a slot and rotation label in the reference public view. -/
def plonkQueryClaim {actions : ℕ} {G : Type*} (pub : PlonkPublicPolynomials actions)
    (x hEval : Fp) (view : PreIpaMaskView 5 (22 * actions + 10) G)
    (id : CommitmentId) (point : Fin 4) : Fp :=
  match id with
  | .instanceCol a c =>
    if ha : a < actions then if c = 0 then (pub.instances ⟨a, ha⟩).eval x else 0 else 0
  | .adviceCol a c =>
    if ha : a < actions then if hc : c < 10 then
      privateColumnView view.2.1 (.advice ⟨a, ha⟩ ⟨c, hc⟩) point.castSucc else 0 else 0
  | .permProduct a s =>
    if ha : a < actions then if hs : s < 3 then
      privateColumnView view.2.1 (.permutationProduct ⟨a, ha⟩ ⟨s, hs⟩) point.castSucc else 0 else 0
  | .lookupProduct a l =>
    if ha : a < actions then if hl : l < 3 then
      privateColumnView view.2.1 (.lookupProduct ⟨a, ha⟩ ⟨l, hl⟩) point.castSucc else 0 else 0
  | .lookupPermInput a l =>
    if ha : a < actions then if hl : l < 3 then
      privateColumnView view.2.1 (.lookupInput ⟨a, ha⟩ ⟨l, hl⟩) point.castSucc else 0 else 0
  | .lookupPermTable a l =>
    if ha : a < actions then if hl : l < 3 then
      privateColumnView view.2.1 (.lookupTable ⟨a, ha⟩ ⟨l, hl⟩) point.castSucc else 0 else 0
  | .fixedCol c => if hc : c < 29 then (pub.fixed ⟨c, hc⟩).eval x else 0
  | .permCommon c => if hc : c < 15 then (pub.sigma ⟨c, hc⟩).eval x else 0
  | .vanishingH => hEval
  | .randomPoly => view.2.2.1

/-- A private slot reads exactly the column observation named by its rotation label. -/
theorem plonkQueryClaim_private {actions : ℕ} {G : Type*} (pub : PlonkPublicPolynomials actions)
    (x hEval : Fp) (view : PreIpaMaskView 5 (22 * actions + 10) G)
    (id : PrivateColumnId actions) (point : Fin 4) :
    plonkQueryClaim pub x hEval view (plonkPrivateCommitmentId id) point =
      privateColumnView view.2.1 id point.castSucc := by
  cases id <;> simp [plonkQueryClaim, plonkPrivateCommitmentId]

/-- The flat query stream carries exactly the reference claims, including the actual inferred quotient. -/
theorem plonkProofFromJointView_queryClaims {actions k : ℕ} {G : Type*} [Inhabited G] [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    (assembleQueries vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch).map
        (fun query : VerifierQuery k Fp G => (query.commId, query.point, query.eval)) =
      (plonkQuerySpine actions).map (fun entry =>
        (entry.1, plonkQueryPoint vk.omega ch.x entry.2,
          plonkQueryClaim pub ch.x (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1))
            view.1 entry.1 entry.2)) := by
  have hquotient := plonkVerifierHx_proof vk pub ch view
  dsimp only [plonkProofShape, FixtureMax.shape] at hquotient ⊢
  simp only [assembleQueries]
  rw [hquotient]
  simp [hlayout.instances, hlayout.advice, hlayout.fixed, hlayout.blinding,
    columnQueries, permutationQueries, lookupQueries, permutationCommonQueries, vanishingQueries,
    plonkProofFromJointView, plonkProofString, plonkProofShape, FixtureMax.shape,
    plonkQuerySpine, plonkPerActionQuerySpine, plonkQueryPoint, plonkQueryRotation, plonkQueryClaim,
    plonkAdviceQueryOrder_eq_vecCons, plonkFixedQueryOrder_eq_vecCons, List.map_append,
    List.map_flatten, List.range_succ, Function.comp_def, rotateOmega]

/-- Every pattern entry is realized by an actual verifier query with the specified scalar claim. -/
theorem plonkProofFromJointView_queryClaim_exists {actions k : ℕ} {G : Type*}
    [Inhabited G] [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (entry : CommitmentId × Fin 4) (hentry : entry ∈ plonkQuerySpine actions) :
    ∃ query ∈ assembleQueries vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch,
      query.commId = entry.1 ∧ query.point = plonkQueryPoint vk.omega ch.x entry.2 ∧
        query.eval = plonkQueryClaim pub ch.x
          (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1 entry.1 entry.2 := by
  have hmem : (entry.1, plonkQueryPoint vk.omega ch.x entry.2,
      plonkQueryClaim pub ch.x (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1))
        view.1 entry.1 entry.2) ∈
      (assembleQueries vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch).map
        (fun query : VerifierQuery k Fp G => (query.commId, query.point, query.eval)) := by
    rw [plonkProofFromJointView_queryClaims vk hlayout pub instanceCommitment ch view]
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
  obtain ⟨query, hquery, heq⟩ := List.mem_map.mp hmem
  exact ⟨query, hquery, congrArg Prod.fst heq,
    congrArg (fun entry : CommitmentId × Fp × Fp => entry.2.1) heq,
    congrArg (fun entry : CommitmentId × Fp × Fp => entry.2.2) heq⟩

/-- The singleton group's slot claims are the existing public, table, quotient, and mask claim list. -/
theorem plonkQueryClaim_firstGroup {actions : ℕ} {G : Type*} (pub : PlonkPublicPolynomials actions)
    (x hEval : Fp) (view : PreIpaMaskView 5 (22 * actions + 10) G) :
    (plonkOpeningCommitmentIds actions 0).map (fun id => plonkQueryClaim pub x hEval view id 0) =
      plonkFirstGroupClaims pub x (privateColumnView view.2.1) hEval view.2.2.1 := by
  simp [plonkOpeningCommitmentIds, plonkFirstGroupClaims, plonkQueryClaim,
    List.map_append, List.map_flatMap, List.map_map, Function.comp_def]

/-- Folding the slot claims at each declared node reconstructs the reference's existing node-value lists. -/
theorem plonkQueryClaims_nodeValues {actions : ℕ} {G : Type*} (pub : PlonkPublicPolynomials actions)
    (x x1 hEval : Fp) (view : PreIpaMaskView 5 (22 * actions + 10) G) (i : Fin 5) :
    (plonkGroupPointLabels i).map (fun point => plonkScalarFold x1
      ((plonkOpeningCommitmentIds actions i).map (fun id => plonkQueryClaim pub x hEval view id point))) =
        plonkPublicNodeValues pub x x1 hEval view i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [plonkGroupPointLabels, Matrix.cons_val_zero, List.map_cons, List.map_nil,
      plonkQueryClaim_firstGroup, plonkPublicNodeValues, Fin.cons_zero]
  · simp only [plonkOpeningCommitmentIds, Fin.cons_succ, List.map_map, Function.comp_def,
      plonkQueryClaim_private, plonkPublicNodeValues]
    rw [← plonkGroupPointLabels_observations j.succ, List.map_map]
    rfl

end Zcash.Snark.ZeroKnowledge
