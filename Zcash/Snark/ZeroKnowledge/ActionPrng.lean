import Zcash.Snark.ZeroKnowledge.ActionRandomnessSource
import Zcash.Snark.ZeroKnowledge.PrngReduction

/-!
# The seeded-tape reduction for the actual Action experiment

The generator and seed law are explicit parameters. One seed produces one
complete raw tape of `148m + 46` draws for one attempt; the theorem makes no
reset or independence assertion about repeated uses of generator state.

The security premise concerns the Boolean output of the displayed reduction,
which runs the reference prover and the supplied view test once. It is not a
statistical-distance premise on the generator's whole output. Instantiating
a concrete PRNG assumption must account for this reduction's resources.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open scoped ENNReal

/-- Run the reference Action computation on one candidate tape and test its full encoded view. -/
noncomputable def actionPrngReduction {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (test : (Challenges urs.k Fp × ProverAttemptResult) → PMF Bool) :
    RawPrivateTape actions → PMF Bool :=
  tapeReduction (widePlonkChallenges urs.k) (actionZkRunFromRawTape urs hk inputs witness) test

/-- The seeded Action view differs from the public simulator by at most protocol plus PRNG-test error. -/
theorem seededActionZk_test_error_bound [Fintype VestaG] {actions : ℕ} {Seed : Type*}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (seeds : PMF Seed) (generate : Seed → RawPrivateTape actions)
    (test : (Challenges urs.k Fp × ProverAttemptResult) → PMF Bool) (η : ℝ≥0∞)
    (prngForward : PMFEventBiasLE
      ((seededTapeSource seeds generate).bind (actionPrngReduction urs hk inputs witness test))
      ((PMF.uniformOfFintype (RawPrivateTape actions)).bind (actionPrngReduction urs hk inputs witness test)) η)
    (prngReverse : PMFEventBiasLE
      ((PMF.uniformOfFintype (RawPrivateTape actions)).bind (actionPrngReduction urs hk inputs witness test))
      ((seededTapeSource seeds generate).bind (actionPrngReduction urs hk inputs witness test)) η) :
    PMFEventBiasLE
        ((actionZkProverFromSource urs hk inputs witness (seededTapeSource seeds generate)).bind test)
        ((actionZkSimulator urs hk inputs).bind test) (plonkSimulationErrorBound actions + η) ∧
      PMFEventBiasLE ((actionZkSimulator urs hk inputs).bind test)
        ((actionZkProverFromSource urs hk inputs witness (seededTapeSource seeds generate)).bind test)
        (plonkSimulationErrorBound actions + η) := by
  have h := wideActionZkRelation_simulation_error_bound urs hk inputs witness hvalid hW
  rw [← actionZkProverFromSource_uniform urs hk inputs witness] at h
  exact seededTape_test_simulation_error_bound (widePlonkChallenges urs.k) seeds generate
    (PMF.uniformOfFintype (RawPrivateTape actions)) (actionZkRunFromRawTape urs hk inputs witness)
    (actionZkSimulator urs hk inputs) test η (plonkSimulationErrorBound actions)
    prngForward prngReverse h.1 h.2

end Zcash.Snark.ZeroKnowledge
