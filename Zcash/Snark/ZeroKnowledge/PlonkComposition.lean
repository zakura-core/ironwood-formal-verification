import Zcash.Snark.ZeroKnowledge.PlonkPublicOpening

/-!
# Joint pre-IPA and IPA simulation

The honest computation retains the full private row state, linear-mask coefficients, and
commitment blinds until the IPA is formed. The simulator receives only the public pre-IPA
view. Pointwise validity of the reconstructed opening lets the IPA simulation be applied
inside the private-state distribution, before replacing that distribution by its public
projection. No conditional independence of the inherited IPA blind is assumed.

The quotient evaluation and degree obligations are required only on row states the honest
construction can produce. They remain premises until the PLONK row and quotient algorithms
are connected to the circuit relation. Challenges are supplied, and failures are not yet
part of this joint algebraic experiment.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open CompPoly

/-- The entire private state needed after sampling the pre-IPA randomness. -/
abbrev PlonkPrivateMaterial (actions : ℕ) :=
  ColumnHistory 2048 × ((Fp × Fp) × (Fin (22 * actions + 10) → Fp))

/-- Independent ideal coins, with all earlier masked rows retained by their constructors. -/
noncomputable def idealPlonkMaterial {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) : PMF (PlonkPrivateMaterial actions) :=
  Zcash.independentProductPMF (idealColumnRows (plonkColumnSteps construct) history)
    (Zcash.independentProductPMF (PMF.uniformOfFintype (Fp × Fp))
      (PMF.uniformOfFintype (Fin (22 * actions + 10) → Fp)))

/-- Pointwise-equal continuations on sampled states give the same distribution, allowing simulation
replacements only where the preceding law can reach. -/
private theorem bind_eq_on_support {A B : Type*} (law : PMF A) (actual simulated : A → PMF B)
    (h : ∀ a ∈ law.support, actual a = simulated a) : law.bind actual = law.bind simulated := by
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ law.support
  · rw [h a ha]
  · have hz : law a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp only [hz, zero_mul]

/-- Every sampled material contains a row state in the honest row construction's support. -/
theorem idealPlonkMaterial_rows_mem {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (material : PlonkPrivateMaterial actions)
    (hmaterial : material ∈ (idealPlonkMaterial construct history).support) :
    material.1 ∈ (idealColumnRows (plonkColumnSteps construct) history).support := by
  rw [idealPlonkMaterial, Zcash.independentProductPMF, PMF.mem_support_bind_iff] at hmaterial
  obtain ⟨rows, hrows, hrest⟩ := hmaterial
  rw [PMF.mem_support_map_iff] at hrest
  obtain ⟨rest, _, heq⟩ := hrest
  simpa only [← heq] using hrows

section Computation

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The complete enriched pre-IPA view of one private material. -/
def plonkMaskViewFromMaterial {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 q : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (material : PlonkPrivateMaterial actions) : PreIpaMaskView 5 (22 * actions + 10) G :=
  honestPlonkMaskView urs pub x x1 x2 q pieces material.1 material.2.1 material.2.2

/-- The actual IPA public input, coefficient vector, and inherited blind, computed from private state. -/
def plonkIpaData {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions) :
    IpaPublic urs.k Fp G × ((Fin (2 ^ urs.k) → Fp) × Fp) :=
  let blinds := plonkCommitmentBlindsFromVector material.2.2
  let groups := plonkBlindedOpeningGroups pub material.1 x x1 (pieces material.1) material.2.1 blinds
  (computedMultiopenIpaPublic urs x2 x4 q xi z blinds.quotientPrime rounds groups,
    polynomialCoefficients (2 ^ urs.k) (multiopenFinalPolynomial x2 x4 groups),
    multiopenFinalBlind x4 blinds.quotientPrime groups)

/-- The actual-core material view has precisely the previously proved joint masking law. -/
theorem idealPlonkMaterial_maskView {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 q : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly) :
    (idealPlonkMaterial construct history).map (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces) =
      idealPreIpaMaskView (plonkColumnSteps construct) history urs.w (omegaOf 11) x q
        (plonkObservationPoints (omegaOf 11) x q) (plonkCommitmentCores urs pub x x1 x2 pieces)
        (fun rows _ => plonkFirstGroupOffset pub rows x x1 q (pieces rows)) := by
  simp only [idealPlonkMaterial, plonkMaskViewFromMaterial, idealPreIpaMaskView,
    Zcash.independentProductPMF, commitmentView, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, PMF.bind_bind, Function.comp_def, honestPlonkMaskView, honestPreIpaMaskView]

end Computation

section JointLaw

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- The actual polynomial commitment cores are hidden together with the scalar trace. -/
theorem idealPlonkMaterial_maskView_simulation {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 q : Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (hW : Function.Bijective (fun r : Fp => r • urs.w))
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) x q))
    (haway : ∀ i : Fin 5, ∀ j : Fin 2048, plonkObservationPoints (omegaOf 11) x q i ≠ omegaOf 11 ^ j.val) :
    (idealPlonkMaterial construct history).map (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces) =
      preIpaMaskSimulator (G := G) 5 (22 * actions) (22 * actions + 10) := by
  rw [idealPlonkMaterial_maskView]
  have hq : q ≠ x := by
    have h := hpoints.ne (by decide : (4 : Fin 5) ≠ 0)
    simpa [plonkObservationPoints] using h
  have hsize (step : ColumnStep 2048) (hstep : step ∈ plonkColumnSteps construct) :
      step.firstMasked + 5 ≤ 2048 := by
    have h := plonkColumnSteps_firstMasked_le construct step hstep
    omega
  have haway' (step : ColumnStep 2048) (hstep : step ∈ plonkColumnSteps construct)
      (i : Fin 5) (j : Fin step.firstMasked) :
      plonkObservationPoints (omegaOf 11) x q i ≠ omegaOf 11 ^ j.val :=
    haway i ⟨j.val, by have h := hsize step hstep; omega⟩
  simpa only [plonkColumnSteps_length] using idealPreIpaMask_simulation_capstone
    (plonkColumnSteps construct) history urs.w (omegaOf 11) x q (plonkObservationPoints (omegaOf 11) x q)
    (plonkCommitmentCores urs pub x x1 x2 pieces)
    (fun rows _ => plonkFirstGroupOffset pub rows x x1 q (pieces rows))
    hW (omegaOf_rows_injective 11 (by decide)) hpoints haway' hsize hq

/-- Honest joint algebraic view, retaining all dependencies between the pre-IPA messages and IPA tail. -/
noncomputable def idealPlonkJointProver {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) :
    PMF (PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G) :=
  (idealPlonkMaterial construct history).bind fun material =>
    let data := plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material
    (idealIpaProver data.1 data.2.1 data.2.2).map
      (Prod.mk (plonkMaskViewFromMaterial urs pub x x1 x2 q pieces material))

/-- Joint simulator: sample the public mask view and simulate the IPA for its reconstructed opening. -/
noncomputable def idealPlonkJointSimulator {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp) :
    PMF (PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G) :=
  (preIpaMaskSimulator (G := G) 5 (22 * actions) (22 * actions + 10)).bind fun view =>
    (idealIpaSimulator (plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx view)).map (Prod.mk view)

/-- The complete ideal algebraic view has one public simulator, provided the honest quotient is consistent.

The row-support premises state exactly which PLONK correctness obligations remain. In
particular, this is not obtained by assuming that the opening witness is independent of
the preceding transcript. -/
theorem idealPlonkJoint_simulation_capstone {actions : ℕ}
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
    idealPlonkJointProver construct history urs pub x x1 x2 x4 q xi z rounds pieces =
      idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx := by
  let observe := plonkMaskViewFromMaterial urs pub x x1 x2 q pieces
  let simulate := fun view : PreIpaMaskView 5 (22 * actions + 10) G =>
    (idealIpaSimulator (plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx view)).map (Prod.mk view)
  have hfixed (material : PlonkPrivateMaterial actions)
      (hm : material ∈ (idealPlonkMaterial construct history).support) :
      let data := plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material
      (idealIpaProver data.1 data.2.1 data.2.2).map (Prod.mk (observe material)) = simulate (observe material) := by
    have hrows := idealPlonkMaterial_rows_mem construct history material hm
    have hi := idealPlonkMultiopenIpa_simulation urs hk pub material.1 x x1 x2 x4 q xi z rounds
      (pieces material.1) material.2.1 (plonkCommitmentBlindsFromVector material.2.2)
      hpoints (hdegree material.1 hrows) hW hxi hu
    have hp := plonkPublicIpaInput_honest urs pub x x1 x2 x4 q xi z rounds expectedHx pieces
      material.1 material.2.1 material.2.2 (hquotient material.1 hrows) hpoints
    dsimp only [plonkIpaData]
    rw [hi]
    simp only [plonkCommitmentBlindsFromVector] at hp ⊢
    rw [← hp]
    rfl
  calc
    _ = (idealPlonkMaterial construct history).bind (simulate ∘ observe) :=
      bind_eq_on_support _ _ _ hfixed
    _ = ((idealPlonkMaterial construct history).map observe).bind simulate := (PMF.bind_map _ _ _).symm
    _ = _ := by
      rw [idealPlonkMaterial_maskView_simulation construct history urs pub x x1 x2 q pieces hW hpoints haway]
      rfl

end JointLaw

end Zcash.Snark.ZeroKnowledge
