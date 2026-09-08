import Zcash.Snark.ZeroKnowledge.PlonkOracle
import Zcash.Snark.ZeroKnowledge.PlonkEncoding
import Zcash.Snark.ZeroKnowledge.RawFieldTape

/-!
# Forgetting the raw hash trace of an independent attempt

The canonical result, including failed prefixes and status, has exactly the
existing encoded-attempt law. This observation does not assert that cached
oracle replies are independent.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- Raw independent replies produce precisely the encoded wide-challenge experiment. -/
theorem rawDigestChallengeExperiment_observed {actions k : ℕ}
    (produce : Challenges k Fp → PMF (ProofString (plonkProofShape actions k) Fp VestaG))
    (initial : List (TranscriptElt Fp VestaG)) :
    (rawDigestChallengeExperiment k produce).map (fun view =>
        (plonkRawOracleView initial view.1 view.2.2).1) =
      ((widePlonkChallenges k).bind (fun ch => (produce ch).map (Prod.mk ch))).map
        (fun view => (encodedPlonkAttempt view).2) := by
  simp only [rawDigestChallengeExperiment, PMF.map_bind, PMF.map_comp,
    Function.comp_def, plonkRawOracleView_result, encodedPlonkAttempt,
    widePlonkChallenges, sampleFieldsWith_eq_independentTape, PMF.bind_map]
  rw [← uniformRawFieldTape_reduce (k + 11)]
  simp only [PMF.bind_map, Function.comp_def, plonkAttemptObservation]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (RawFieldTape (k + 11))))
  funext digests
  rfl

end Zcash.Snark.ZeroKnowledge
