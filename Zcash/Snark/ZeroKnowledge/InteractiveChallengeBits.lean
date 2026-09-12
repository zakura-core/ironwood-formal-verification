import Zcash.Snark.ZeroKnowledge.StoredHistoryChallengeCost
import Zcash.Snark.ZeroKnowledge.StoredBitTapeCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- A complete stored raw history supplies the original challenge record in its exact receive order. -/
theorem plonkHistoryChallenges_ofFn {k : ℕ} (replies : PlonkChallengeTape k (Fin challengeDigestCard)) :
    plonkChallengesFromDigests k (oracleHistoryTape 0 (List.ofFn replies)) =
      plonkChallengesFromTape (reduceFieldTape replies) := by
  apply congrArg (plonkChallengesFromTape (k := k))
  funext index
  have h := getDListCosted_ofFn_result 0 (0 : Fin challengeDigestCard) replies index
  rewrite [getDListCosted_result] at h
  exact congrArg (fun word : Fin challengeDigestCard => (word.val : Fp)) h

/-- Uniform raw verifier words have precisely the original wide-reduced challenge law. -/
theorem uniformRawPlonkChallenges (k : ℕ) :
    (PMF.uniformOfFintype (PlonkChallengeTape k (Fin challengeDigestCard))).map
      (fun replies => plonkChallengesFromTape (reduceFieldTape replies)) = widePlonkChallenges k :=
  rawFieldTape_sample_law (k + 11) plonkChallengesFromTape

/-- A fixed fair-bit verifier tape produces that same law, retaining all 512 bits in each word. -/
theorem uniformBitPlonkChallenges (k : ℕ) :
    (PMF.uniformOfFintype (Fin ((k + 11) * 512) → Bool)).map
      (fun bits => plonkChallengesFromTape (reduceFieldTape (rawBitsTapeEquiv (k + 11) bits))) =
      widePlonkChallenges k := by
  have h := congrArg (PMF.map (fun replies : PlonkChallengeTape k (Fin challengeDigestCard) =>
    plonkChallengesFromTape (reduceFieldTape replies))) (Zcash.map_uniformOfFintype_equiv (rawBitsTapeEquiv (k + 11)))
  rewrite [PMF.map_comp, uniformRawPlonkChallenges] at h
  exact h

end Zcash.Snark.ZeroKnowledge
