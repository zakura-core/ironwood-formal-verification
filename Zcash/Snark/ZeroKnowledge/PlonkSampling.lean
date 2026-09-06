import Zcash.Snark.ZeroKnowledge.PlonkComposition

/-!
# The full batched prover tape and its joint simulation bound

The source's pre-IPA batch layout is converted by the existing tape equivalences into
row masks, linear coefficients, and commitment blinds. The remaining suffix is the
ordered IPA tape. Reindexing equal-sized `Fin` types changes no field entry.

This is a single deterministic computation on all `148m + 46` prover field samples.
Replacing that complete tape by ideal field samples therefore transfers the joint
simulation theorem without assuming independence between the two emitted transcript parts.
The same quotient/degree and supplied-challenge premises remain explicit.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open CompPoly
open Zcash.Common
open scoped ENNReal

/-- Separate the actual pre-IPA batches, changing only the types of equal-sized index sets. -/
def plonkPreIpaCoinsEquiv {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    (Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp) ≃
      ((Fin (columnRowSampleCount (plonkColumnSteps construct)) → Fp) ×
        ((Fp × Fp) × (Fin (22 * actions + 10) → Fp))) :=
  let rowIndices := finCongr (congrArg columnRowSampleCount (plonkColumnBatches_flatten construct))
  let blindIndices := finCongr (show (plonkColumnBatches construct).flatten.length + 10 = 22 * actions + 10 by
    rw [plonkColumnBatches_flatten, plonkColumnSteps_length])
  (batchedPreIpaTapeEquiv (plonkColumnBatches construct)).trans
    ((preIpaCoinEquiv (plonkColumnBatches construct).flatten).trans
      (Equiv.prodCongr (Equiv.arrowCongr rowIndices (Equiv.refl Fp))
        (Equiv.prodCongr (Equiv.refl (Fp × Fp)) (Equiv.arrowCongr blindIndices (Equiv.refl Fp)))))

/-- Compute the complete private material from the actual pre-IPA field subsequence. -/
def plonkMaterialFromTape {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp) :
    PlonkPrivateMaterial actions :=
  let coins := plonkPreIpaCoinsEquiv construct tape
  (columnRowsFromTape (plonkColumnSteps construct) history coins.1, coins.2)

/-- Uniform batched fields realize the exact ideal private-state law used in the joint proof. -/
theorem uniformTapePlonkMaterial {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) :
    (PMF.uniformOfFintype (Fin (batchedColumnSampleCount (plonkColumnBatches construct) + 12) → Fp)).map
        (plonkMaterialFromTape construct history) = idealPlonkMaterial construct history := by
  change (PMF.uniformOfFintype _).map
    ((fun coins => (columnRowsFromTape (plonkColumnSteps construct) history coins.1, coins.2)) ∘
      plonkPreIpaCoinsEquiv construct) = _
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    ← Zcash.independentProductPMF_uniform
      (A := Fin (columnRowSampleCount (plonkColumnSteps construct)) → Fp)
      (B := (Fp × Fp) × (Fin (22 * actions + 10) → Fp)),
    ← Zcash.independentProductPMF_uniform (A := Fp × Fp) (B := Fin (22 * actions + 10) → Fp),
    Zcash.independentProductPMF_map_left, uniformTapeColumnRows]
  rfl

/-- The pre-IPA batches followed by the complete ordered IPA suffix. -/
def plonkJointSampleCount {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) (k : ℕ) : ℕ :=
  batchedColumnSampleCount (plonkColumnBatches construct) + 12 + ipaSampleCount k

/-- The actual eleven-round tape has exactly the pinned `148m + 46` field draws. -/
theorem plonkJointSampleCount_eq {actions k : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) (hk : k = 11) :
    plonkJointSampleCount construct k = fieldSampleCount actions := by
  subst k
  exact plonk_and_ipa_sample_count construct

section Computation

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Compute both transcript parts from a single complete tape, retaining their actual shared private state. -/
def plonkJointViewFromTape {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (tape : Fin (plonkJointSampleCount construct urs.k) → Fp) :
    PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G :=
  let split := splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct) + 12) (ipaSampleCount urs.k) Fp tape
  let material := plonkMaterialFromTape construct history split.1
  let data := plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material
  (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material,
    ipaTranscriptFromTape data.1 data.2.1 data.2.2 split.2)

end Computation

section JointLaw

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- Uniform complete tapes realize the same honest joint law as the separated private-state model. -/
theorem uniformTapePlonkJoint {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) :
    (PMF.uniformOfFintype (Fin (plonkJointSampleCount construct urs.k) → Fp)).map
        (plonkJointViewFromTape construct history urs pub x x1 x2 x4 q xi z rounds pieces) =
      idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces := by
  let materialize := plonkMaterialFromTape construct history
  let observe := plonkMaskViewFromMaterial urs pub x x1 x2 q pieces
  let opening := plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces
  let finish := fun material : PlonkPrivateMaterial actions =>
    (idealIpaProver (opening material).1 (opening material).2.1 (opening material).2.2).map
      (Prod.mk (observe material))
  have htail (material : PlonkPrivateMaterial actions) :
      (PMF.uniformOfFintype (Fin (ipaSampleCount urs.k) → Fp)).map
          (fun tape => (observe material, ipaTranscriptFromTape
            (opening material).1 (opening material).2.1 (opening material).2.2 tape)) = finish material := by
    dsimp only [finish]
    rw [← uniformTapeIpa_eq_idealProver (opening material).1 (opening material).2.1 (opening material).2.2,
      PMF.map_comp]
    rfl
  change (PMF.uniformOfFintype _).map
    ((fun tapes => (observe (materialize tapes.1), ipaTranscriptFromTape
      (opening (materialize tapes.1)).1 (opening (materialize tapes.1)).2.1
      (opening (materialize tapes.1)).2.2 tapes.2)) ∘
      splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct) + 12) (ipaSampleCount urs.k) Fp) = _
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    ← Zcash.independentProductPMF_uniform, Zcash.independentProductPMF, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  simp_rw [htail]
  change (PMF.uniformOfFintype _).bind (finish ∘ materialize) = _
  rw [← PMF.bind_map, uniformTapePlonkMaterial]
  rfl

/-- The actual wide-reduced field law, used by the complete deterministic algebraic prover model. -/
noncomputable def sampledPlonkJointProver {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) :
    PMF (PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G) :=
  (sampleFieldsWith (plonkJointSampleCount construct urs.k)
    (plonkJointViewFromTape construct history urs pub x x1 x2 x4 q xi z rounds pieces)).runFreshPMF fieldSample

/-- Joint simulation for the complete field tape, with one reduction-bias charge per actual draw. -/
theorem sampledPlonkJoint_simulation_error_bound {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (hk : urs.k = 11) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp)
    (hdegree : ∀ rows ∈ (idealColumnRows (plonkColumnSteps construct) history).support,
      PlonkDegreeBounds pub (pieces rows))
    (hquotient : ∀ rows ∈ (idealColumnRows (plonkColumnSteps construct) history).support,
      (plonkCollapsedQuotient x (pieces rows)).eval x =
        expectedHx (privateColumnView (observeColumnRows (omegaOf 11) (plonkObservationPoints (omegaOf 11) x q) rows)))
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) (hxi : xi ≠ 0) (hu : ∀ j, rounds j ≠ 0)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) x q))
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048, plonkObservationPoints (omegaOf 11) x q i ≠ omegaOf 11 ^ j.val) :
    PMFEventBiasLE (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        (idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx)
        ((fieldSampleCount actions : ℕ) * challenge255Bias) ∧
      PMFEventBiasLE (idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx)
        (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces)
        ((fieldSampleCount actions : ℕ) * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (plonkJointSampleCount construct urs.k)
    (plonkJointViewFromTape construct history urs pub x x1 x2 x4 q xi z rounds pieces)
  rw [uniformTapePlonkJoint, idealPlonkJoint_simulation_capstone construct history urs hk pub
    x x1 x2 x4 q xi z rounds pieces expectedHx hdegree hquotient hW hxi hu hpoints haway] at h
  change PMFEventBiasLE (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces) _ _ ∧
    PMFEventBiasLE _ (sampledPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces) _ at h
  rw [plonkJointSampleCount_eq construct hk] at h
  exact h

end JointLaw

end Zcash.Snark.ZeroKnowledge
