import Zcash.Snark.ZeroKnowledge.PlonkKeygenFixed
import Zcash.Snark.ZeroKnowledge.PlonkOriginalSimulation

/-!
# Reference simulation with compiler-derived fixed polynomials

This endpoint uses the actual keygen fixed-row constructor and interpolates every
public polynomial from rows. The compiler supplies the zero masking suffix, the
interpolants supply all public degree bounds, and a finite check reads the remaining
two fixed boundary rows directly from keygen.

The Action specialization of that check, sigma/copy and instance-row provenance,
public commitments, full verifier routing, codecs, failures, native execution, and
the Fiat-Shamir/PRNG model remain outside this conditional reference theorem.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

/-- Numerical joint simulation using compiler fixed rows and row-derived public degree bounds. -/
theorem wideKeygenPlonkVerifier_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (htopK : top.domainExponent = 11) (htopBlind : top.blindingFactors = 5)
    (htopColumns : 29 ≤ top.fixedColumnCount)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (degree : PlonkDegreeProfile vk)
    (hmask : plonkMaskBoundaryCheck vk (plonkKeygenMaskBoundaryFixed top) = true)
    (hvalid : PlonkOriginalRowsValid vk (plonkKeygenPublicPolynomials top instances sigma) witness)
    (copies : List (PlonkCopyCell vk.permutationChunks × PlonkCopyCell vk.permutationChunks))
    (hcopy : PlonkCopyWitness vk (plonkKeygenPublicPolynomials top instances sigma) witness copies)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hchunks : vk.permutationChunks.length = 3) (hpacked : vk.permutationChunks.flatten.length = 15)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    let pub := plonkKeygenPublicPolynomials top instances sigma
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
  obtain ⟨hinstance, hfixed, hsigma⟩ :=
    plonkPublicPolynomialsFromRows_degree instances (plonkKeygenFixedRows top) sigma
  exact wideOriginalValidPlonkVerifier_simulation_error_bound urs hk vk
    (plonkKeygenPublicPolynomials top instances sigma) witness degree
    (plonkKeygenPublicPolynomials_maskingProfile top htopK htopBlind htopColumns instances sigma vk hmask)
    hvalid copies hcopy homega hn hblind hchunks hpacked hinstance hfixed hsigma hW

end Zcash.Snark.ZeroKnowledge
