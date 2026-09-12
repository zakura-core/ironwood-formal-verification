import Zcash.Snark.ZeroKnowledge.PlonkSimulator
import Zcash.Snark.ZeroKnowledge.PlonkQuotientSimulation
import Zcash.Snark.ZeroKnowledge.IpaSampling

/-!
# A flat tape for the executable joint simulator

The simulator uses field coins for its commitment points, five observations per
private column, two masked scalars, two points per IPA round, and two final IPA
scalars. The tape is rearranged by explicit computable equivalences; it does not
enumerate points or search for discrete logarithms.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)

/-- The pre-IPA simulator's complete field draw count. -/
def plonkMaskSimulatorSampleCount (actions : ℕ) : ℕ :=
  (22 * actions + 10) + (22 * actions * 5 + 2)

/-- Split pre-IPA field draws into point coins, observation vectors, and two scalar coins. -/
def plonkMaskSimulatorTapeEquiv (actions : ℕ) :
    (Fin (plonkMaskSimulatorSampleCount actions) → Fp) ≃ PlonkMaskSimulatorCoins actions :=
  (splitTapeEquiv (22 * actions + 10) (22 * actions * 5 + 2) Fp).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((splitTapeEquiv (22 * actions * 5) 2 Fp).trans
        (Equiv.prodCongr
          ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Fp)).trans
            (Equiv.curry (Fin (22 * actions)) (Fin 5) Fp))
          (finTwoArrowEquiv Fp))))

/-- The joint simulator's complete field draw count, including the IPA suffix. -/
def plonkSimulatorSampleCount (actions k : ℕ) : ℕ :=
  plonkMaskSimulatorSampleCount actions + ((k * 2 + 1) + 1)

/-- There are `132m + 2k + 14` field draws in the executable joint simulator. -/
theorem plonkSimulatorSampleCount_eq (actions k : ℕ) :
    plonkSimulatorSampleCount actions k = 132 * actions + 2 * k + 14 := by
  unfold plonkSimulatorSampleCount plonkMaskSimulatorSampleCount
  omega

/-- Eleven rounds require exactly `132m + 36` uniform simulator field draws. -/
theorem plonkSimulatorSampleCount_eleven (actions : ℕ) :
    plonkSimulatorSampleCount actions 11 = 132 * actions + 36 := by
  rw [plonkSimulatorSampleCount_eq]

/-- Rearrange the whole simulator tape into the coins of its existing executable implementation. -/
def plonkSimulatorTapeEquiv (actions k : ℕ) :
    (Fin (plonkSimulatorSampleCount actions k) → Fp) ≃
      (PlonkMaskSimulatorCoins actions × (((Fin k → Fp × Fp) × Fp) × Fp)) :=
  (splitTapeEquiv (plonkMaskSimulatorSampleCount actions) ((k * 2 + 1) + 1) Fp).trans
    (Equiv.prodCongr (plonkMaskSimulatorTapeEquiv actions)
      ((splitTapeEquiv (k * 2 + 1) 1 Fp).trans
        (Equiv.prodCongr
          ((splitTapeEquiv (k * 2) 1 Fp).trans
            (Equiv.prodCongr (roundPairTapeEquiv k Fp) (Equiv.funUnique (Fin 1) Fp)))
          (Equiv.funUnique (Fin 1) Fp))))

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Execute the existing verifier-shaped public simulator on a flat field tape. -/
def plonkVerifierSimulatorFromTape {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (tape : Fin (plonkSimulatorSampleCount actions urs.k) → Fp) :
    ProofString (plonkProofShape actions urs.k) Fp G :=
  let coins := plonkSimulatorTapeEquiv actions urs.k tape
  plonkProofFromJointView pub ch.x ch.x1
    (plonkJointSimulatorFromCoins urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
      ch.ipaRound (plonkVerifierHx vk pub ch) coins.1 coins.2.1.1 coins.2.2 coins.2.1.2)

/-- Uniform flat simulator fields implement exactly the joint simulator in the comparison theorem. -/
theorem plonkVerifierSimulatorFromTape_law [Fintype G] {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    (PMF.uniformOfFintype (Fin (plonkSimulatorSampleCount actions urs.k) → Fp)).map
        (plonkVerifierSimulatorFromTape urs vk pub ch) = idealPlonkVerifierSimulator urs vk pub ch := by
  rw [idealPlonkVerifierSimulator,
    ← idealPlonkJointSimulatorFromFieldCoins_eq urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
      ch.ipaRound (plonkVerifierHx vk pub ch) hW,
    idealPlonkJointSimulatorFromFieldCoins_program]
  change (PMF.uniformOfFintype _).map
    ((fun coins : PlonkMaskSimulatorCoins actions × (((Fin urs.k → Fp × Fp) × Fp) × Fp) =>
      plonkProofFromJointView pub ch.x ch.x1
        (plonkJointSimulatorFromCoins urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
          ch.ipaRound (plonkVerifierHx vk pub ch) coins.1 coins.2.1.1 coins.2.2 coins.2.1.2)) ∘
      plonkSimulatorTapeEquiv actions urs.k) = _
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    ← Zcash.independentProductPMF_uniform (A := PlonkMaskSimulatorCoins actions)
      (B := ((Fin urs.k → Fp × Fp) × Fp) × Fp),
    ← Zcash.independentProductPMF_uniform (A := (Fin urs.k → Fp × Fp) × Fp) (B := Fp)]
  simp only [Zcash.independentProductPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]

end Zcash.Snark.ZeroKnowledge
