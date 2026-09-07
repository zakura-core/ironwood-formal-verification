import Zcash.Snark.ZeroKnowledge.PlonkReferenceRowLaw
import Zcash.Snark.ZeroKnowledge.PlonkFreshBounds

/-!
# Joint simulation with the concrete reference row algorithms

The remaining row error is now the probability of failed sorting, failed gate
preservation, or failure of the packed copy-product identity. The product denominator
exceptions are derived from the same complete independent challenge law and contribute
`42882m/p + 2 × bias`. Together with the earlier challenge and prover-tape terms this
gives `(42882m + 4113)/p + (148m + 70) × bias`, plus the explicit prerequisite failures.

The experiment still uses the total reference constructor and typed algebraic proof
view. A valid-witness theorem for the remaining prerequisites, whole-prover failures
and codecs, the online schedule, Fiat-Shamir, and native Rust correspondence remain
separate obligations. No failure event is conditioned away.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

/-- The concrete reference row algorithms supply the denominator term in the full joint simulation bound. -/
theorem wideConstructedPlonkVerifier_simulation_error_bound {actions : ℕ} {G : Type*}
    [AddCommGroup G] [Module Fp G] [Fintype G]
    (urs : URS G) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hchunks : vk.permutationChunks.length = 3) (hpacked : vk.permutationChunks.flatten.length = 15)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    PMFEventBiasLE
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub)
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
      (plonkRowPrerequisiteFailureMass (widePlonkChallenges urs.k) vk pub witness +
        (((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) ∧
    PMFEventBiasLE
      (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
      (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub)
      (plonkRowPrerequisiteFailureMass (widePlonkChallenges urs.k) vk pub witness +
        (((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias)) := by
  have h := wideFreshPlonkVerifier_simulation_error_bound urs (plonkTotalColumnConstructor vk pub witness)
    [] hk vk pub profile homega hn hblind hinstance hfixed hsigma hW
  have hrows := freshPlonkInvalidRowMass_le_prerequisites urs vk pub witness hchunks
  have hcount : (vk.permutationChunks.flatten.length + 6) * actions * 2042 = 42882 * actions := by
    rw [hpacked]
    omega
  rw [hcount] at hrows
  have herror : freshPlonkInvalidRowMass urs (widePlonkChallenges urs.k)
        (plonkTotalColumnConstructor vk pub witness) [] vk pub +
        (4113 : ℝ≥0∞) / scalarFieldOrder + (((148 * actions + 68 : ℕ) : ℝ≥0∞) * challenge255Bias) ≤
      plonkRowPrerequisiteFailureMass (widePlonkChallenges urs.k) vk pub witness +
        (((42882 * actions + 4113 : ℕ) : ℝ≥0∞) / scalarFieldOrder) +
          (((148 * actions + 70 : ℕ) : ℝ≥0∞) * challenge255Bias) := by
    calc
      _ ≤ (plonkRowPrerequisiteFailureMass (widePlonkChallenges urs.k) vk pub witness +
          (((42882 * actions : ℕ) : ℝ≥0∞) / scalarFieldOrder) + 2 * challenge255Bias) +
          (4113 : ℝ≥0∞) / scalarFieldOrder + (((148 * actions + 68 : ℕ) : ℝ≥0∞) * challenge255Bias) :=
        add_le_add (add_le_add hrows le_rfl) le_rfl
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
        ring
  exact ⟨fun event => (h.1 event).trans (add_le_add le_rfl herror),
    fun event => (h.2 event).trans (add_le_add le_rfl herror)⟩

end Zcash.Snark.ZeroKnowledge
