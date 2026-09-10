import Zcash.Snark.ZeroKnowledge.PlonkKeygenSelectors
import Zcash.Snark.ZeroKnowledge.PlonkOriginalSimulation

/-!
# Reference simulation from the compiler's initial packed selectors

This named sufficient-condition result applies to circuits whose four designated
initial packed selectors are zero. Interpolation supplies the public degree bounds;
selector-only expression certificates and V1 placement supply the mask profile.
Boundary values in the fourteen original fixed columns are unrestricted. The
compiler's row accessor pads out-of-range rows and columns with zero.

The theorem takes the instance and sigma rows, original-row validity, copy validity,
key dimensions, and a bijective blinding map as explicit inputs. The deployed Action
result in ActionCompilerSimulation uses its checked fixed-value boundary profile.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

/-- Numerical joint simulation with the compiler mask obligations reduced to its initial selectors. -/
theorem wideSelectorKeygenPlonkVerifier_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    (htopPrefix : top.constraintSystem.numFixedColumns ≤ 14)
    (hplacement : Halo2.FloorPlanner.V1.placementEnd top.operations ≤ 2041)
    (hfirst : ∀ column : Fin 29, column.val ∈ plonkInitialMaskColumns →
      plonkKeygenFixedRows top column 0 = 0)
    (instances : Fin actions → Fin 2048 → Fp) (sigma : Fin 15 → Fin 2048 → Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (degree : PlonkDegreeProfile vk)
    (hmask : plonkPartialMaskBoundaryCheck vk plonkSelectorBoundaryKnown = true)
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
    (plonkKeygenPublicPolynomials_selectorMaskingProfile top htopPrefix
      hplacement hfirst instances sigma vk hmask)
    hvalid copies hcopy homega hn hblind hchunks hpacked hinstance hfixed hsigma hW

end Zcash.Snark.ZeroKnowledge
