import Zcash.Snark.ZeroKnowledge.ActionOracleModel
import Zcash.Snark.ZeroKnowledge.PlonkSimulatorTape

/-!
# Executing the Action oracle simulator from bounded tapes

Raw-digest recovery has an equivalent implementation: choose the raw challenge
tape first, reduce it to field challenges, and run the public simulator on
those challenges. Its original raw tape can then be programmed directly.

The executable simulator uses twenty-two uniform 512-bit words and `132m + 36`
uniform field draws at eleven rounds. The real prover's fields remain wide
reduced; only this witness-free simulator uses ideal field coins. The field
draw count is a sampling-resource bound, not a machine-instruction count.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open Zcash.Circuits.Action
open Zcash.Common

/-- The lifted simulator can sample and keep its raw challenge tape before simulating the proof. -/
theorem actionZkDigestSimulator_raw_law [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp) :
    actionZkDigestSimulator urs hk inputs =
      rawDigestChallengeExperiment urs.k
        (idealPlonkVerifierSimulator urs
          (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
          (actionPublicPolynomials inputs)) :=
  attachPlonkDigests_wideChallenges _ _

/-- Compute a programmed attempt using only public data, a raw challenge tape, and simulator field coins. -/
def actionOracleSimulatorFromTapes {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (digests : PlonkChallengeTape urs.k (Fin challengeDigestCard))
    (fields : Fin (plonkSimulatorSampleCount actions urs.k) → Fp) :
    Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :=
  let ch := plonkChallengesFromTape (fun i => ((digests i).val : Fp))
  let proof := plonkVerifierSimulatorFromTape urs
    (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
    (actionPublicPolynomials inputs) ch fields
  programOracleView cache (plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) digests proof)

/-- Sample the two finite tapes and execute the computable witness-free oracle simulator. -/
noncomputable def actionOracleSimulatorProgram {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    PMF (Option (ProverAttemptResult × OracleCache TranscriptHashAddress (Fin challengeDigestCard))) :=
  (PMF.uniformOfFintype (PlonkChallengeTape urs.k (Fin challengeDigestCard))).bind fun digests =>
    (sampleFieldsWith (plonkSimulatorSampleCount actions urs.k)
      (actionOracleSimulatorFromTapes urs hk inputs vkTranscriptRepr cache digests)).runFreshPMF idealFieldSample

/-- The bounded-tape implementation has exactly the simulator law in the oracle comparison. -/
theorem actionOracleSimulatorProgram_law [Fintype VestaG] {actions : ℕ}
    (urs : URS VestaG) (hk : urs.k = 11) (inputs : Fin actions → PublicInputs Fp)
    (hW : urs.w ≠ 0) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard)) :
    actionOracleSimulatorProgram urs hk inputs vkTranscriptRepr cache =
      actionOracleSimulator urs hk inputs vkTranscriptRepr cache := by
  unfold actionOracleSimulatorProgram actionOracleSimulator
  rw [actionZkDigestSimulator_raw_law]
  simp only [rawDigestChallengeExperiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (PlonkChallengeTape urs.k (Fin challengeDigestCard))))
  funext digests
  rw [sampleFieldsWith_uniform]
  have h := congrArg (PMF.map (fun proof => programOracleView cache
    (plonkRawOracleView (actionOracleInitial urs vkTranscriptRepr inputs) digests proof)))
    (plonkVerifierSimulatorFromTape_law urs
      (actionReferenceKey (actions := actions) urs hk actionCircuit_newFixedCols_eq_fifteen)
      (actionPublicPolynomials inputs) (plonkChallengesFromTape (fun i => ((digests i).val : Fp)))
      (vestaBlinding_bijective urs.w hW))
  simpa only [PMF.map_comp, Function.comp_def, actionOracleSimulatorFromTapes, actionOracleProgramView] using h

/-- The simulator's actual field-sampling program respects the derived `132m + 36` budget. -/
theorem actionOracleSimulator_field_queryBound {actions : ℕ} (urs : URS VestaG) (hk : urs.k = 11)
    (inputs : Fin actions → PublicInputs Fp) (vkTranscriptRepr : Fp)
    (cache : OracleCache TranscriptHashAddress (Fin challengeDigestCard))
    (digests : PlonkChallengeTape urs.k (Fin challengeDigestCard)) :
    (sampleFieldsWith (plonkSimulatorSampleCount actions urs.k)
      (actionOracleSimulatorFromTapes urs hk inputs vkTranscriptRepr cache digests)).QueryBound
      (132 * actions + 36) := by
  apply (sampleFieldsWith_queryBound _ _).mono
  rw [hk, plonkSimulatorSampleCount_eleven]

end Zcash.Snark.ZeroKnowledge
