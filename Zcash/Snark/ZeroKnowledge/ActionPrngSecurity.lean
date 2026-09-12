import Zcash.Snark.ZeroKnowledge.ActionPrng
import Zcash.Snark.ZeroKnowledge.PrngSecurityReduction

/-!
# The Action simulation under an explicit computational PRNG assumption

One uniform seed generates exactly the private tape of `148m + 46` raw 512-bit
words. Auxiliary data and the verifier's coins are independent of that seed.
The tested view includes the full challenge tape, emitted prefix, and status.

The PRNG security premise ranges over a supplied admissible class. The theorem
requires membership of the actual reference-prover reduction, including its
view test. `CostedInteractivePrng` discharges membership for finite executable
view circuits with complete structural runtime bounds. Generator security is
still an external assumption; this one-attempt template does not address
repeated generator state.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open scoped ENNReal

/-- The complete Action distinguishing experiment is exactly the PRNG game for its actual reduction. -/
theorem actionPrngSecurity_game_law {actions : ℕ} {Aux : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (auxiliary : PMF Aux)
    (source : PMF (RawPrivateTape actions))
    (test : Aux → (Challenges urs.k Fp × ProverAttemptResult) → PMF Bool) :
    auxiliary.bind (fun aux => (actionZkProverFromSource urs hk inputs witness source).bind (test aux)) =
      auxiliaryPrngGame auxiliary source (fun aux => actionPrngReduction urs hk inputs witness (test aux)) :=
  auxiliaryPrngGame_reduction_law auxiliary source (fun _ => widePlonkChallenges urs.k)
    (fun _ => actionZkRunFromRawTape urs hk inputs witness) test

/-- For every admitted reduction, the seeded Action experiment has test advantage at most `epsilon(m) + eta`. -/
theorem uniformSeedActionZk_test_error_bound [Fintype VestaG] {actions : ℕ} {Aux : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (auxiliary : PMF Aux) (seedBits : ℕ) (generate : (Fin seedBits → Bool) → RawPrivateTape actions)
    (test : Aux → (Challenges urs.k Fp × ProverAttemptResult) → PMF Bool)
    (admissible : Set (Aux → RawPrivateTape actions → PMF Bool)) (η : ℝ≥0∞)
    (secure : UniformSeedPrngSecure seedBits generate auxiliary admissible η)
    (hclass : (fun aux => actionPrngReduction urs hk inputs witness (test aux)) ∈ admissible) :
    PMFEventBiasLE
        (auxiliary.bind (fun aux => (actionZkProverFromSource urs hk inputs witness
          (uniformSeedTapeSource seedBits generate)).bind (test aux)))
        (auxiliary.bind (fun aux => (actionZkSimulator urs hk inputs).bind (test aux)))
        (plonkSimulationErrorBound actions + η) ∧
      PMFEventBiasLE (auxiliary.bind (fun aux => (actionZkSimulator urs hk inputs).bind (test aux)))
        (auxiliary.bind (fun aux => (actionZkProverFromSource urs hk inputs witness
          (uniformSeedTapeSource seedBits generate)).bind (test aux)))
        (plonkSimulationErrorBound actions + η) := by
  have h := wideActionZkRelation_simulation_error_bound urs hk inputs witness hvalid hW
  rw [← actionZkProverFromSource_uniform urs hk inputs witness] at h
  exact uniformSeedPrng_simulation_error_bound auxiliary seedBits generate
    (fun _ => widePlonkChallenges urs.k) (fun _ => actionZkRunFromRawTape urs hk inputs witness)
    (fun _ => actionZkSimulator urs hk inputs) test admissible η (plonkSimulationErrorBound actions)
    secure hclass (fun _ _ => h)

end Zcash.Snark.ZeroKnowledge
