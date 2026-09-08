import Zcash.Snark.ZeroKnowledge.ActionOracleModel
import Zcash.Snark.ZeroKnowledge.PlonkAnchor
import Zcash.Snark.ZeroKnowledge.AnchorProbability

/-!
# The cost of earlier oracle queries

Every query from a nonempty Action proof contains its first advice commitment.
One existing byte address can name at most one such point, and the simulator's
point is exactly uniform. Internal queries are distinct. Thus `q` cached
addresses cause programming failure with probability at most `q / p`.

Composing on the simulator's exceptional event charges the complete interactive
simulation error only once. This statement includes incomplete attempts and
all exceptional field challenges.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS scalarFieldOrder card_Fp)
open Zcash.Circuits.Action
open Zcash.Common
open scoped ENNReal

/-- Failed programming of a nonempty proof requires a prior address naming its first advice point. -/
theorem plonkRawOracleView_failure_anchor {actions k : ℕ}
    (initial : List (TranscriptElt Fp VestaG))
    (digests : PlonkChallengeTape k (Fin challengeDigestCard))
    (proof : ProofString (plonkProofShape actions k) Fp VestaG) (hpositive : 0 < actions)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (hfailure : programOracleView cache (plonkRawOracleView initial digests proof) = none) :
    ∃ address ∈ cache.map Prod.fst,
      HasTranscriptAnchor initial address (proof.adviceCommitments ⟨0, hpositive⟩ (0 : Fin 10)) := by
  classical
  by_contra hnone
  have hfresh : ∀ address ∈ (plonkRawOracleView initial digests proof).2.map Prod.fst,
      address ∉ cache.map Prod.fst := by
    intro address haddress hcache
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp haddress
    obtain ⟨rest, htrace⟩ := plonkAttemptTrace_firstAdvice proof hpositive
    have hanchor : HasTranscriptAnchor initial entry.1
        (proof.adviceCommitments ⟨0, hpositive⟩ (0 : Fin 10)) := by
      unfold plonkRawOracleView at hentry
      rw [htrace] at hentry
      exact protocolOracleView_queries_anchor _ _ _ _ _ _ entry hentry
    exact hnone ⟨entry.1, hcache, hanchor⟩
  have hgood := programOracleTrace_ne_none_of_fresh
    (plonkRawOracleView initial digests proof).2 cache
    (plonkRawOracleView_queries_nodup initial digests proof) hfresh
  exact hgood (Option.map_eq_none_iff.mp hfailure)

/-- The complete raw-digest Action simulator retains an exactly uniform first private commitment. -/
theorem actionOracleSimulator_firstAdvice [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (hpositive : 0 < actions) :
    (actionZkDigestSimulator urs hk inputs).map
        (fun view => view.2.2.adviceCommitments ⟨0, hpositive⟩ (0 : Fin 10)) =
      PMF.uniformOfFintype VestaG :=
  digestPlonkVerifierSimulator_advice urs _ _ _ _ _

/-- Earlier byte queries contribute at most one inverse field order each, with no extra sampling-bias term. -/
theorem actionOracle_programming_failure_le [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    (actionZkDigestSimulator urs hk inputs).toOuterMeasure
        {view | actionOracleProgramView urs vkTranscriptRepr inputs cache view = none} ≤
      (cache.length : ℝ≥0∞) / scalarFieldOrder := by
  have hcard : Fintype.card VestaG = scalarFieldOrder := by
    rw [← Fintype.card_congr (Equiv.ofBijective (fun r : Fp => r • urs.w)
      (vestaBlinding_bijective urs.w hW)), card_Fp]
  have hatom (point : VestaG) :
      PMF.uniformOfFintype VestaG point ≤ (scalarFieldOrder : ℝ≥0∞)⁻¹ := by
    rw [PMF.uniformOfFintype_apply, hcard]
  let anchor := fun view : PlonkChallengeTape urs.k (Fin challengeDigestCard) ×
      PlonkFreshView actions urs.k VestaG =>
    view.2.2.adviceCommitments ⟨0, hpositive⟩ (0 : Fin 10)
  calc
    _ ≤ (actionZkDigestSimulator urs hk inputs).toOuterMeasure
        (anchor ⁻¹' {point | ∃ address ∈ cache.map Prod.fst,
          HasTranscriptAnchor (actionOracleInitial urs vkTranscriptRepr inputs) address point}) := by
      apply PMF.toOuterMeasure_mono
      intro view hview
      exact plonkRawOracleView_failure_anchor _ _ _ hpositive cache hview.1
    _ = (PMF.uniformOfFintype VestaG).toOuterMeasure
        {point | ∃ address ∈ cache.map Prod.fst,
          HasTranscriptAnchor (actionOracleInitial urs vkTranscriptRepr inputs) address point} := by
      rw [← PMF.toOuterMeasure_map_apply, actionOracleSimulator_firstAdvice]
    _ ≤ (cache.map Prod.fst).length * (scalarFieldOrder : ℝ≥0∞)⁻¹ :=
      transcriptAnchorList_mass_le _ hatom _ _
    _ = _ := by rw [List.length_map, div_eq_mul_inv]

/-- One complete cached-oracle attempt has two-sided error `epsilon(m) + q / p`. -/
theorem actionOracle_cached_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (hvalid : ActionZkRelation urs hk inputs witness)
    (hpositive : 0 < actions) (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    let error := plonkSimulationErrorBound actions + (cache.length : ℝ≥0∞) / scalarFieldOrder
    PMFEventBiasLE (actionOracleProver urs hk inputs witness vkTranscriptRepr cache)
        (actionOracleSimulator urs hk inputs vkTranscriptRepr cache) error ∧
      PMFEventBiasLE (actionOracleSimulator urs hk inputs vkTranscriptRepr cache)
        (actionOracleProver urs hk inputs witness vkTranscriptRepr cache) error := by
  have h := actionOracle_simulation_error_bound urs hk inputs witness hvalid hW vkTranscriptRepr cache
  have herror := actionOracle_programming_failure_le urs hk inputs hpositive hW vkTranscriptRepr cache
  constructor
  · intro event
    exact (h.1 event).trans (add_le_add le_rfl (add_le_add le_rfl herror))
  · intro event
    exact (h.2 event).trans (add_le_add le_rfl (add_le_add le_rfl herror))

end Zcash.Snark.ZeroKnowledge
