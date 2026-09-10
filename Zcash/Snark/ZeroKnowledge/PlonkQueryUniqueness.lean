import Zcash.Snark.ZeroKnowledge.PlonkVerifierGrouping
import Mathlib.Data.List.Nodup

/-!
# The verifier's duplicate-query guard

Every commitment-slot and rotation-label pair occurs at most once. Injective
interpretation of the labels therefore makes the actual duplicate-query guard
succeed, which permits the verifier's existing evaluation-faithfulness lemmas.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The duplicate-query check is equivalent to uniqueness of commitment-ID and point pairs, exposing
the combinatorial acceptance condition. -/
private theorem queryPairs_nodup {k : ℕ} {F G : Type*} [DecidableEq F]
    (queries : List (VerifierQuery k F G)) :
    hasDuplicateCommitmentPoint queries = false ↔
      (queries.map (fun query => (query.commId, query.point))).Nodup := by
  induction queries with
  | nil => simp [hasDuplicateCommitmentPoint]
  | cons query queries ih =>
    simp [hasDuplicateCommitmentPoint, List.nodup_cons, ih, List.mem_map,
      Prod.mk.injEq, List.any_eq_false]

/-- The first Action's query spine has no repeated ID-point pair, supplying the base case for
multi-Action query uniqueness. -/
private theorem firstActionQueryPairs : (plonkPerActionQuerySpine 0).Nodup := by
  decide +kernel

/-- Every local commitment-slot and rotation-label pair is queried exactly once when present. -/
theorem plonkPerActionQuerySpine_nodup (a : ℕ) : (plonkPerActionQuerySpine a).Nodup := by
  rw [plonkPerActionQuerySpine_shift]
  refine firstActionQueryPairs.map ?_
  intro left right h
  exact Prod.ext (plonkShiftCommitmentId_injective a (Prod.mk.inj h).1) (Prod.mk.inj h).2

/-- The shared query suffix has no duplicate slot-point pair. -/
theorem plonkSharedQuerySpine_nodup : plonkSharedQuerySpine.Nodup :=
  plonkSharedCommitmentOrder_nodup.map (fun _ _ h => congrArg Prod.fst h)

/-- Pair uniqueness composes across all disjoint Action blocks and the shared suffix. -/
theorem plonkQuerySpine_nodup (actions : ℕ) : (plonkQuerySpine actions).Nodup := by
  rw [plonkQuerySpine_eq_blocks]
  have hblocks : ((List.finRange actions).flatMap
      (fun a => plonkPerActionQuerySpine a.val)).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun a _ => plonkPerActionQuerySpine_nodup a.val, (List.nodup_finRange actions).imp ?_⟩
    intro a b hab entry ha hb
    exact plonkPerActionQuerySpine_disjoint a.val b.val (fun h => hab (Fin.ext h))
      (List.mem_map.mpr ⟨entry, ha, rfl⟩) (List.mem_map.mpr ⟨entry, hb, rfl⟩)
  have hdisjoint : List.Disjoint ((List.finRange actions).flatMap
      (fun a => plonkPerActionQuerySpine a.val)) plonkSharedQuerySpine := by
    intro entry hlocal hshared
    obtain ⟨a, _, hentry⟩ := List.mem_flatMap.mp hlocal
    obtain ⟨id, hid, hpair⟩ := List.mem_map.mp hshared
    have ha := plonkPerActionQuerySpine_action a.val hentry
    have hs := plonkSharedCommitmentOrder_action hid
    have hidEq : id = entry.1 := congrArg Prod.fst hpair
    rw [hidEq, ha] at hs
    contradiction
  exact List.nodup_append.mpr ⟨hblocks, plonkSharedQuerySpine_nodup,
    fun _ hleft _ hright h => hdisjoint (h ▸ hleft) hright⟩

/-- The finite query pattern always passes the actual duplicate-query check. -/
theorem plonkQueryPattern_noDuplicates (actions k : ℕ) :
    hasDuplicateCommitmentPoint (plonkQueryPattern actions k) = false := by
  apply (queryPairs_nodup _).mpr
  rw [plonkQueryPattern, List.map_map]
  exact (plonkQuerySpine_nodup actions).map (fun _ _ h =>
    Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- The reference proof's actual queries pass the duplicate guard on distinct rotation points. -/
theorem plonkVerifierGroup_noDuplicates {actions k : ℕ} {G : Type*} [Inhabited G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch) = false := by
  exact (plonkProofFromJointView_duplicateQueries vk hlayout pub instanceCommitment ch view hpoints).trans
    (plonkQueryPattern_noDuplicates actions k)

/-- The rejecting grouping function returns the already-derived grouping on this query path. -/
theorem plonkVerifierGroup_duplicateGuard {actions k : ℕ} {G : Type*}
    [Inhabited G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    let queries := assembleQueries vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch
    constructIntermediateSets? queries = some (constructIntermediateSets queries) := by
  dsimp only
  rw [constructIntermediateSets?,
    plonkVerifierGroup_noDuplicates vk hlayout pub instanceCommitment ch view hpoints]
  rfl

end Zcash.Snark.ZeroKnowledge
