import Zcash.Snark.ZeroKnowledge.PlonkValidRows
import Zcash.Snark.ZeroKnowledge.PlonkCopySimulation

/-!
# Numerical joint simulation from original satisfying rows

Original gates, lookup tuples, and copy equations supply the reference row conditions
when the public expression-mask and sigma profiles hold. The unbounded row failure
term disappears; only the established sampling and exceptional-challenge terms remain.

This is still a theorem about the total reference constructor and typed algebraic
proof under fresh independent wide-reduced challenges. Instantiating the public
profiles for the captured circuit, matching the full verifier's grouping and codecs,
whole-prover failure behavior, Fiat-Shamir, and the native Rust implementation are
separate obligations. No distribution is conditioned on successful construction.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

/-- Original valid rows give the explicit numerical error for the joint reference proof simulation. -/
theorem wideOriginalValidPlonkVerifier_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (degree : PlonkDegreeProfile vk)
    (masking : PlonkMaskingProfile vk pub) (hvalid : PlonkOriginalRowsValid vk pub witness)
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
      ((((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) ∧
    PMFEventBiasLE
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub)
      ((((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
        (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) := by
  have h := wideCopyValidPlonkVerifier_simulation_error_bound urs hk vk pub witness degree copies hcopy
    homega hn hblind hchunks hpacked hinstance hfixed hsigma hW
  rw [plonkGateConstructionFailureMass_eq_zero (widePlonkChallenges urs.k) vk pub witness masking hvalid,
    _root_.zero_add] at h
  exact h

end Zcash.Snark.ZeroKnowledge
