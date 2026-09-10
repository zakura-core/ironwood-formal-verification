import Zcash.Snark.ZeroKnowledge.IpaSimulation
import Zcash.Snark.ZeroKnowledge.Sampling

/-!
# The IPA stage under wide-reduced field sampling

The tape order is `k` sparse coefficients, one mask-commitment blind, then a left/right
blind pair for each round. This is `3k+1` draws, or 34 for the pinned `k = 11` stage.
The same computed transcript is run under the exact reduction law and the ideal law.

The simulation bound is for supplied public challenges and the raw group transcript.
It must not be read as a bound after conditioning a Fiat–Shamir execution on its challenges.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

/-- Consecutive pairs in a flat tape supply the left and right blinds of each round. -/
def roundPairTapeEquiv (k : ℕ) (F : Type*) :
    (Fin (k * 2) → F) ≃ (Fin k → F × F) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl F)).trans
    ((Equiv.curry (Fin k) (Fin 2) F).trans
      (Equiv.piCongrRight fun _ => finTwoArrowEquiv F))

/-- The IPA stage's exact count, grouped in its consumption order. -/
def ipaSampleCount (k : ℕ) : ℕ := k + (k * 2 + 1)

/-- The IPA consumes three samples per round and one final sample, supplying its contribution to
prover randomness accounting. -/
theorem ipaSampleCount_eq (k : ℕ) : ipaSampleCount k = 3 * k + 1 := by
  unfold ipaSampleCount
  omega

/-- The deployed eleven-round IPA consumes 34 field samples, specializing the generic randomness
count. -/
theorem ipaSampleCount_eleven : ipaSampleCount 11 = 34 := rfl

/-- Turn the ordered IPA tape into the sparse coefficients and all independent blinds. -/
def ipaTapeEquiv (k : ℕ) (F : Type*) :
    (Fin (ipaSampleCount k) → F) ≃ ((Fin k → F) × IpaBlinds k F) :=
  (splitTapeEquiv k (k * 2 + 1) F).trans
    (Equiv.prodCongr (Equiv.refl (Fin k → F))
      ((Fin.consEquiv (fun _ : Fin (k * 2 + 1) => F)).symm.trans
        (Equiv.prodCongr (Equiv.refl F) (roundPairTapeEquiv k F))))

/-- Sparse coefficients are read from the first `k` tape entries. -/
theorem ipaTapeEquiv_alphas {k : ℕ} {F : Type*} (tape : Fin (ipaSampleCount k) → F)
    (t : Fin k) :
    (ipaTapeEquiv k F tape).1 t = tape ⟨t.val, by unfold ipaSampleCount; omega⟩ := rfl

/-- The mask-commitment blind immediately follows the sparse coefficients. -/
theorem ipaTapeEquiv_maskBlind {k : ℕ} {F : Type*} (tape : Fin (ipaSampleCount k) → F) :
    (ipaTapeEquiv k F tape).2.1 = tape ⟨k, by unfold ipaSampleCount; omega⟩ := by
  change tape ⟨k + 0, _⟩ = _
  congr 1

/-- Round `j` reads left then right, immediately after the mask-commitment blind. -/
theorem ipaTapeEquiv_roundBlinds {k : ℕ} {F : Type*} (tape : Fin (ipaSampleCount k) → F)
    (j : Fin k) :
    (ipaTapeEquiv k F tape).2.2 j =
      (tape ⟨k + 1 + 2 * j.val, by unfold ipaSampleCount; have hj := j.isLt; omega⟩,
        tape ⟨k + 2 + 2 * j.val, by unfold ipaSampleCount; have hj := j.isLt; omega⟩) := by
  apply Prod.ext
  · change tape ⟨k + (0 + 2 * j.val + 1), _⟩ = _
    apply congrArg tape
    apply Fin.ext
    change k + (0 + 2 * j.val + 1) = k + 1 + 2 * j.val
    omega
  · change tape ⟨k + (1 + 2 * j.val + 1), _⟩ = _
    apply congrArg tape
    apply Fin.ext
    change k + (1 + 2 * j.val + 1) = k + 2 + 2 * j.val
    omega

section Transcript

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The honest IPA computation on the ordered tape, with supplied public challenges. -/
def ipaTranscriptFromTape {k : ℕ} (pub : IpaPublic k F G)
    (coefficients : Fin (2 ^ k) → F) (rho : F)
    (tape : Fin (ipaSampleCount k) → F) : IpaTranscript k F G :=
  let coins := ipaTapeEquiv k F tape
  honestIpaTranscript pub coefficients rho coins.1 coins.2

/-- A uniform flat tape is exactly the independent ideal coins used in the joint proof. -/
theorem uniformTapeIpa_eq_idealProver [Fintype F] [Fintype G] {k : ℕ}
    (pub : IpaPublic k F G) (coefficients : Fin (2 ^ k) → F) (rho : F) :
    (PMF.uniformOfFintype (Fin (ipaSampleCount k) → F)).map
        (ipaTranscriptFromTape pub coefficients rho) = idealIpaProver pub coefficients rho := by
  change (PMF.uniformOfFintype (Fin (ipaSampleCount k) → F)).map
    ((fun coins : (Fin k → F) × IpaBlinds k F =>
      honestIpaTranscript pub coefficients rho coins.1 coins.2) ∘ ipaTapeEquiv k F) = _
  rw [← PMF.map_comp, Zcash.map_uniformOfFintype_equiv,
    ← Zcash.independentProductPMF_uniform]
  simp [Zcash.independentProductPMF, PMF.map_bind, PMF.map_comp,
    Function.comp_def, idealIpaProver]

end Transcript

section WideReduction

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- The raw IPA computation with actual wide-reduced samples and fixed public challenges. -/
noncomputable def sampledIpaProver {k : ℕ} (pub : IpaPublic k Fp G)
    (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) : PMF (IpaTranscript k Fp G) :=
  (sampleFieldsWith (ipaSampleCount k) (ipaTranscriptFromTape pub coefficients rho)).runFreshPMF
    fieldSample

/-- Replacing all IPA samples is bounded even at zero challenges or an invalid opening.

This only compares the same computation under two coin laws, before using any simulation
theorem. In particular the challenge exceptions remain present on both sides. -/
theorem sampledIpaProver_ideal_error_bound {k : ℕ} (pub : IpaPublic k Fp G)
    (coefficients : Fin (2 ^ k) → Fp) (rho : Fp) :
    PMFEventBiasLE (sampledIpaProver pub coefficients rho) (idealIpaProver pub coefficients rho)
        (ipaSampleCount k * challenge255Bias) ∧
      PMFEventBiasLE (idealIpaProver pub coefficients rho) (sampledIpaProver pub coefficients rho)
        (ipaSampleCount k * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (ipaSampleCount k)
    (ipaTranscriptFromTape pub coefficients rho)
  rw [uniformTapeIpa_eq_idealProver] at h
  exact h

/-- The entire IPA transcript is within `(3k+1) × bias` of its witness-free simulator.

This accounts for every IPA mask and blind, including correlations with `f`. The premises
and scope of `idealIpa_simulation_capstone` remain explicit; no encoding or challenge event
has been silently conditioned away. -/
theorem sampledIpa_simulation_error_bound {k : ℕ} (pub : IpaPublic k Fp G)
    (coefficients : Fin (2 ^ k) → Fp) (rho : Fp)
    (hW : Function.Bijective (fun r : Fp => r • pub.W)) (hxi : pub.xi ≠ 0)
    (hcommit : pub.commitment = commitGen pub.generators coefficients + rho • pub.W)
    (hv : coefficientEvaluation k pub.point coefficients = pub.value)
    (hu : ∀ j, pub.rounds j ≠ 0) :
    PMFEventBiasLE (sampledIpaProver pub coefficients rho) (idealIpaSimulator pub)
        ((3 * k + 1) * challenge255Bias) ∧
      PMFEventBiasLE (idealIpaSimulator pub) (sampledIpaProver pub coefficients rho)
        ((3 * k + 1) * challenge255Bias) := by
  have h := sampleFieldsWith_error_bound (ipaSampleCount k)
    (ipaTranscriptFromTape pub coefficients rho)
  rw [uniformTapeIpa_eq_idealProver,
    idealIpa_simulation_capstone pub coefficients rho hW hxi hcommit hv hu] at h
  change PMFEventBiasLE (sampledIpaProver pub coefficients rho) (idealIpaSimulator pub)
      (ipaSampleCount k * challenge255Bias) ∧
    PMFEventBiasLE (idealIpaSimulator pub) (sampledIpaProver pub coefficients rho)
      (ipaSampleCount k * challenge255Bias) at h
  simpa [ipaSampleCount_eq] using h

end WideReduction

end Zcash.Snark.ZeroKnowledge
