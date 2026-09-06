import Zcash.Snark.ZeroKnowledge.PlonkFresh
import Zcash.Snark.ZeroKnowledge.PlonkChallengeBounds

/-!
# Concrete challenge and sampling terms in the full joint comparison

For the fixed size-2048 domain and eleven IPA rounds, the challenge exception term
is at most `4113/p + 22 × bias`. Adding the prover's `148m + 46` field samples gives
`4113/p + (148m + 68) × bias`, in addition to the average invalid-row probability.
The latter is deliberately retained: honest lookup and product correctness, including
zero-denominator executions, has not been supplied by a premise.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf scalarFieldOrder URS)
open Zcash.Common
open scoped ENNReal

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- The full fresh-coin comparison with the numerical challenge-event count and both tape budgets.

This still retains row inconsistency as an explicit probability, and remains an algebraic
interactive experiment without the full prover's codecs, retries, or Fiat–Shamir hashes. -/
theorem wideFreshPlonkVerifier_simulation_error_bound {actions : ℕ} (urs : URS G)
    (construct : Challenges urs.k Fp → PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (hk : urs.k = 11)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (profile : PlonkDegreeProfile vk)
    (homega : vk.omega = omegaOf 11) (hn : vk.n = 2048) (hblind : vk.blindingFactors = 5)
    (hinstance : ∀ a, (pub.instances a).natDegree < 2048)
    (hfixed : ∀ c, (pub.fixed c).natDegree < 2048) (hsigma : ∀ c, (pub.sigma c).natDegree < 2048)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) :
    PMFEventBiasLE (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k) construct history vk pub)
        (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
        (freshPlonkInvalidRowMass urs (widePlonkChallenges urs.k) construct history vk pub +
          (4113 : ℝ≥0∞) / scalarFieldOrder +
            (((148 * actions + 68 : ℕ) : ℝ≥0∞) * challenge255Bias)) ∧
      PMFEventBiasLE (freshPlonkVerifierSimulator urs (widePlonkChallenges urs.k) vk pub)
        (freshSampledPlonkVerifierProver urs (widePlonkChallenges urs.k) construct history vk pub)
        (freshPlonkInvalidRowMass urs (widePlonkChallenges urs.k) construct history vk pub +
          (4113 : ℝ≥0∞) / scalarFieldOrder +
            (((148 * actions + 68 : ℕ) : ℝ≥0∞) * challenge255Bias)) := by
  have h := freshPlonkVerifier_simulation_error_bound urs (widePlonkChallenges urs.k)
    construct history hk vk pub profile homega hn hblind hinstance hfixed hsigma hW
  have hc : (widePlonkChallenges urs.k).toOuterMeasure {ch | ¬ PlonkChallengesGood ch} ≤
      (4113 : ℝ≥0∞) / scalarFieldOrder + 22 * challenge255Bias := by
    simpa only [hk] using widePlonkChallenges_bad_le urs.k
  have hbound : (widePlonkChallenges urs.k).toOuterMeasure {ch | ¬ PlonkChallengesGood ch} +
        freshPlonkInvalidRowMass urs (widePlonkChallenges urs.k) construct history vk pub +
        (fieldSampleCount actions : ℕ) * challenge255Bias ≤
      freshPlonkInvalidRowMass urs (widePlonkChallenges urs.k) construct history vk pub +
        (4113 : ℝ≥0∞) / scalarFieldOrder +
          (((148 * actions + 68 : ℕ) : ℝ≥0∞) * challenge255Bias) := by
    calc
      _ ≤ ((4113 : ℝ≥0∞) / scalarFieldOrder + 22 * challenge255Bias) +
          freshPlonkInvalidRowMass urs (widePlonkChallenges urs.k) construct history vk pub +
          (fieldSampleCount actions : ℕ) * challenge255Bias :=
        add_le_add (add_le_add hc le_rfl) le_rfl
      _ = _ := by
        simp only [fieldSampleCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        ring
  exact ⟨fun event => (h.1 event).trans (add_le_add le_rfl hbound),
    fun event => (h.2 event).trans (add_le_add le_rfl hbound)⟩

end Zcash.Snark.ZeroKnowledge
