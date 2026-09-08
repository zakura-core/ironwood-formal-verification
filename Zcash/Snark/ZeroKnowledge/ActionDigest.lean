import Zcash.Snark.ZeroKnowledge.ActionTyped
import Zcash.Snark.ZeroKnowledge.PlonkDigest

/-!
# The Action reference view with uniform raw challenge digests

The real law samples a raw digest tape, reduces it into the typed challenges,
and runs the same fixed-size reference private-tape program. The simulator
recovers a correctly distributed raw digest for every simulated field challenge.
Their complete joint views retain the original error bound.

These are independent digest tapes. The subsequent Fiat–Shamir argument must
connect them to a consistent oracle queried at the actual message prefixes.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common

/-- Run the exact reference tape program with a complete independent uniform raw challenge tape. -/
noncomputable def actionZkDigestProver {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    PMF (PlonkChallengeTape urs.k (Fin challengeDigestCard) × PlonkFreshView actions urs.k VestaG) :=
  let vk := actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen
  let pub := actionPublicPolynomials inputs
  rawDigestChallengeExperiment urs.k fun ch =>
    (sampleFieldsWith (fieldSampleCount actions)
      (plonkReferenceProofFromTape urs hk vk pub witness ch)).runFreshPMF fieldSample

/-- Add exact raw digest preimages to the public Action simulator. -/
noncomputable def actionZkDigestSimulator [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp) :
    PMF (PlonkChallengeTape urs.k (Fin challengeDigestCard) × PlonkFreshView actions urs.k VestaG) :=
  attachPlonkDigests (actionZkTypedSimulator urs hk inputs)

/-- The raw-tape reference law is exactly the original typed prover lifted through digest recovery. -/
theorem actionZkTypedProver_digest_law [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    attachPlonkDigests (actionZkTypedProver urs hk inputs witness) = actionZkDigestProver urs hk inputs witness := by
  unfold actionZkTypedProver freshSampledPlonkVerifierProver
  rw [attachPlonkDigests_wideChallenges]
  simp only [actionZkDigestProver, plonkReferenceProofFromTape_law]

/-- Exposing correctly distributed raw challenge responses adds no error to the Action simulation. -/
theorem wideActionZkDigest_simulation_error_bound [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hvalid : ActionZkRelation urs hk inputs witness) (hW : urs.w ≠ 0) :
    PMFEventBiasLE (actionZkDigestProver urs hk inputs witness) (actionZkDigestSimulator urs hk inputs)
        (plonkSimulationErrorBound actions) ∧
      PMFEventBiasLE (actionZkDigestSimulator urs hk inputs) (actionZkDigestProver urs hk inputs witness)
        (plonkSimulationErrorBound actions) := by
  have h := wideActionZkTyped_simulation_error_bound urs hk inputs witness hvalid hW
  have hd := liftDigestTapeView_error_bound (fun view => plonkChallengeFields view.1) h.1 h.2
  change PMFEventBiasLE (attachPlonkDigests _) (attachPlonkDigests _) _ ∧
    PMFEventBiasLE (attachPlonkDigests _) (attachPlonkDigests _) _ at hd
  rw [actionZkTypedProver_digest_law] at hd
  exact hd

end Zcash.Snark.ZeroKnowledge
