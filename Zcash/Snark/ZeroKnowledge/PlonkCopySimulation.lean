import Zcash.Snark.ZeroKnowledge.PlonkCopyPrerequisites
import Zcash.Snark.ZeroKnowledge.PlonkConstructedSimulation

/-!
# Joint simulation with valid original copy equations

The packed product identity is derived from original witness copies and public
sigma coherence for every tape. Only construction and gate failures remain in the
row prerequisite probability. Their probability is still unbounded; the experiment
still uses the total reference constructor and the typed algebraic verifier view.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

/-- Original copy equations remove copy products from the remaining joint simulation error. -/
theorem wideCopyValidPlonkVerifier_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (profile : PlonkDegreeProfile vk)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk pub witness copies)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hchunks : vk.permutationChunks.length = 3) (hpacked : vk.permutationChunks.flatten.length = 15)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    PMFEventBiasLE
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub)
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
      (plonkGateConstructionFailureMass (widePlonkChallenges urs.k) vk pub witness +
        (((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) ∧
    PMFEventBiasLE
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub)
      (plonkGateConstructionFailureMass (widePlonkChallenges urs.k) vk pub witness +
        (((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) := by
  have h := wideConstructedPlonkVerifier_simulation_error_bound urs hk vk pub witness profile
    homega hn hblind hchunks hpacked hinstance hfixed hsigma hW
  rw [plonkRowPrerequisiteFailureMass_eq_of_copy (widePlonkChallenges urs.k) vk pub witness copies hcopy] at h
  exact h

end Zcash.Snark.ZeroKnowledge
