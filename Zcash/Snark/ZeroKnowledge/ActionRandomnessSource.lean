import Zcash.Snark.ZeroKnowledge.ActionInstantiation
import Zcash.Snark.ZeroKnowledge.RandomTapeSource

/-!
# The concrete Action prover under an explicit private randomness source

The source supplies a complete raw tape of `148m + 46` 512-bit integers.
The independent verifier tape and the deterministic prover are unchanged.
Uniform raw tapes have exactly the existing reference law. A joint statistical
bound on a replacement source adds to the existing simulation error.

No source is assumed independent internally: all correlations must be accounted
for by its whole-tape comparison. The source is an explicit distribution sampled
independently of the verifier coins for the fixed statement and witness.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common
open scoped ENNReal

/-- The existing reference computation, with wide reduction made explicit at its tape boundary. -/
def actionZkRunFromRawTape {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (ch : Challenges urs.k Fp) (tape : RawPrivateTape actions) :
    Challenges urs.k Fp × ProverAttemptResult :=
  plonkReferenceAttemptFromTape urs hk
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs) witness ch (reducePrivateTape tape)

/-- The Action experiment with an arbitrary joint law for its complete private raw tape. -/
noncomputable def actionZkProverFromSource {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (source : PMF (RawPrivateTape actions)) : PMF (Challenges urs.k Fp × ProverAttemptResult) :=
  sourceTapeExperiment (widePlonkChallenges urs.k) source (actionZkRunFromRawTape urs hk inputs witness)

/-- The raw uniform source is the exact reference law, including all wide-reduction bias and failures. -/
theorem actionZkProverFromSource_uniform {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    actionZkProverFromSource urs hk inputs witness (PMF.uniformOfFintype (RawPrivateTape actions)) =
      actionZkProver urs hk inputs witness := by
  unfold actionZkProverFromSource sourceTapeExperiment actionZkProver freshEncodedPlonkReferenceAttempt
  congr 1
  funext ch
  rw [sampleFieldsWith_eq_independentTape]
  change (PMF.uniformOfFintype (RawPrivateTape actions)).map
    ((plonkReferenceAttemptFromTape urs hk _ _ witness ch) ∘ reducePrivateTape) = _
  rw [← PMF.map_comp, uniformRawPrivateTape_reduce]

/-- Whole-tape source error adds to the established concrete Action simulation bound. -/
theorem sourceActionZk_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0)
    (source : PMF (RawPrivateTape actions)) (η : ℝ≥0∞)
    (forward : PMFEventBiasLE source (PMF.uniformOfFintype (RawPrivateTape actions)) η)
    (reverse : PMFEventBiasLE (PMF.uniformOfFintype (RawPrivateTape actions)) source η) :
    PMFEventBiasLE (actionZkProverFromSource urs hk inputs witness source)
        (actionZkSimulator urs hk inputs) (plonkSimulationErrorBound actions + η) ∧
      PMFEventBiasLE (actionZkSimulator urs hk inputs)
        (actionZkProverFromSource urs hk inputs witness source) (plonkSimulationErrorBound actions + η) := by
  have h := wideActionZkRelation_simulation_error_bound urs hk inputs witness hvalid hW
  rw [← actionZkProverFromSource_uniform urs hk inputs witness] at h
  exact sourceTapeExperiment_simulation_error_bound (widePlonkChallenges urs.k) forward reverse
    (actionZkRunFromRawTape urs hk inputs witness) h.1 h.2

end Zcash.Snark.ZeroKnowledge
